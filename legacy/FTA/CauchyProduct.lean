import FTA.CauchyProductCore
import Mathlib.Tactic.LinearCombination

/-!
# Constructive finite Cauchy product closure

This second half of the Cauchy-product development contains the finite
coordinated-center search, the executable product partition, gcd-transfer
lemmas, and the complete auxiliary product formula.  The analytic event
construction lives in `FTA.CauchyProductCore`; the module boundary keeps
ordinary Lean elaboration within a stable memory footprint.
-/

namespace FTA.CauchyProduct

open FTA.ComputablePolynomial
open ComputablePolynomial.DensePolynomial
open FTA.RationalPolynomialBounds
open FTA.Sturm

namespace FiniteSign

/-- Finite quadrant-transition pattern forced by `NarrowComplexTurn` when
all four endpoint coordinates are nonzero.  If exactly one coordinate sign
changes, the cross-product sign records the forced turn orientation. -/
def SmallTurnCompatible
    (Aₗ Bₗ Aᵣ Bᵣ turn : FiniteSign) : Prop :=
  Aₗ ≠ .zero ∧ Bₗ ≠ .zero ∧ Aᵣ ≠ .zero ∧ Bᵣ ≠ .zero ∧
    if Aₗ = Aᵣ then
      if Bₗ = Bᵣ then True
      else turn = neg (mul Aₗ Bₗ)
    else Bₗ = Bᵣ ∧ turn = mul Aₗ Bₗ

instance (Aₗ Bₗ Aᵣ Bᵣ turn : FiniteSign) :
    Decidable (SmallTurnCompatible Aₗ Bₗ Aᵣ Bᵣ turn) := by
  unfold SmallTurnCompatible
  infer_instance

/-- The three possible coordinate-change patterns of a small turn whose four
endpoint coordinates are nonzero. -/
private inductive SmallTurnShape where
  | same
  | realChange
  | imagChange
deriving DecidableEq, Repr

/-- Apply a small-turn shape to its left endpoint. -/
private def applySmallTurnShape
    (shape : SmallTurnShape) (real imag : FiniteSign) :
    FiniteSign × FiniteSign :=
  match shape with
  | .same => (real, imag)
  | .realChange => (neg real, imag)
  | .imagChange => (real, neg imag)

/-- Read the coordinate-change shape from two endpoints. -/
private def smallTurnShape
    (realLeft imagLeft realRight imagRight : FiniteSign) : SmallTurnShape :=
  if realLeft = realRight then
    if imagLeft = imagRight then .same else .imagChange
  else .realChange

/-- A compatible small turn is recovered exactly by applying its shape to
the left endpoint. -/
private theorem apply_smallTurnShape_eq_of_compatible
    (Aₗ Bₗ Aᵣ Bᵣ turn : FiniteSign)
    (h : SmallTurnCompatible Aₗ Bₗ Aᵣ Bᵣ turn) :
    applySmallTurnShape (smallTurnShape Aₗ Bₗ Aᵣ Bᵣ) Aₗ Bₗ =
      (Aᵣ, Bᵣ) := by
  decide +revert

theorem ofRat_eq_of_mul_pos {x y : ℚ} (hxy : 0 < x * y) :
    ofRat x = ofRat y := by
  apply value_injective
  simp only [value_ofRat]
  exact ratSign_eq_of_mul_pos hxy

theorem ofRat_ne_of_mul_neg {x y : ℚ} (hxy : x * y < 0) :
    ofRat x ≠ ofRat y := by
  rcases mul_neg_iff.mp hxy with ⟨hx, hy⟩ | ⟨hx, hy⟩
  · rw [ofRat_of_pos hx, ofRat_of_neg hy]
    decide
  · rw [ofRat_of_neg hx, ofRat_of_pos hy]
    decide

/-- Positive endpoint dot product induces exactly the finite quadrant
transition relation used by the exhaustive center table; the exact cross
sign records the turn orientation. -/
theorem smallTurnCompatible_of_dot_pos
    {Aₗ Bₗ Aᵣ Bᵣ : ℚ}
    (hAₗ : Aₗ ≠ 0) (hBₗ : Bₗ ≠ 0)
    (hAᵣ : Aᵣ ≠ 0) (hBᵣ : Bᵣ ≠ 0)
    (hdot : 0 < Aₗ * Aᵣ + Bₗ * Bᵣ) :
    SmallTurnCompatible
      (ofRat Aₗ) (ofRat Bₗ) (ofRat Aᵣ) (ofRat Bᵣ)
      (ofRat (Aₗ * Bᵣ - Bₗ * Aᵣ)) := by
  let cross := Aₗ * Bᵣ - Bₗ * Aᵣ
  have hAProduct : Aₗ * Aᵣ ≠ 0 := _root_.mul_ne_zero hAₗ hAᵣ
  have hBProduct : Bₗ * Bᵣ ≠ 0 := _root_.mul_ne_zero hBₗ hBᵣ
  have hAₗSign : ofRat Aₗ ≠ .zero := by
    simpa [ofRat_eq_zero_iff] using hAₗ
  have hBₗSign : ofRat Bₗ ≠ .zero := by
    simpa [ofRat_eq_zero_iff] using hBₗ
  have hAᵣSign : ofRat Aᵣ ≠ .zero := by
    simpa [ofRat_eq_zero_iff] using hAᵣ
  have hBᵣSign : ofRat Bᵣ ≠ .zero := by
    simpa [ofRat_eq_zero_iff] using hBᵣ
  refine ⟨hAₗSign, hBₗSign, hAᵣSign, hBᵣSign, ?_⟩
  rcases lt_or_gt_of_ne hAProduct with hAneg | hApos <;>
    rcases lt_or_gt_of_ne hBProduct with hBneg | hBpos
  · exfalso
    exact (not_lt_of_ge (add_nonpos hAneg.le hBneg.le)) hdot
  · have hAne := ofRat_ne_of_mul_neg hAneg
    have hBeq := ofRat_eq_of_mul_pos hBpos
    have hfirst : 0 < Aₗ ^ 2 * (Bₗ * Bᵣ) :=
      mul_pos (sq_pos_of_ne_zero hAₗ) hBpos
    have hsecond : 0 < -(Bₗ ^ 2 * (Aₗ * Aᵣ)) :=
      neg_pos.mpr (mul_neg_of_pos_of_neg (sq_pos_of_ne_zero hBₗ) hAneg)
    have hcrossProduct : 0 < cross * (Aₗ * Bₗ) := by
      dsimp only [cross]
      nlinarith
    have hturn : ofRat cross = mul (ofRat Aₗ) (ofRat Bₗ) := by
      simpa only [ofRat_mul] using ofRat_eq_of_mul_pos hcrossProduct
    rw [if_neg hAne]
    exact ⟨hBeq, by simpa only [cross] using hturn⟩
  · have hAeq := ofRat_eq_of_mul_pos hApos
    have hBne := ofRat_ne_of_mul_neg hBneg
    have hfirst : 0 < -(Aₗ ^ 2 * (Bₗ * Bᵣ)) :=
      neg_pos.mpr (mul_neg_of_pos_of_neg (sq_pos_of_ne_zero hAₗ) hBneg)
    have hsecond : 0 < Bₗ ^ 2 * (Aₗ * Aᵣ) :=
      mul_pos (sq_pos_of_ne_zero hBₗ) hApos
    have hcrossProduct : 0 < cross * (-(Aₗ * Bₗ)) := by
      dsimp only [cross]
      nlinarith
    have hturn : ofRat cross = neg (mul (ofRat Aₗ) (ofRat Bₗ)) := by
      simpa only [ofRat_neg, ofRat_mul] using
        ofRat_eq_of_mul_pos hcrossProduct
    rw [if_pos hAeq, if_neg hBne]
    simpa only [cross] using hturn
  · have hAeq := ofRat_eq_of_mul_pos hApos
    have hBeq := ofRat_eq_of_mul_pos hBpos
    rw [if_pos hAeq, if_pos hBeq]
    trivial

theorem smallTurnCompatible_of_narrowComplexTurn
    {Aₗ Bₗ Aᵣ Bᵣ : ℚ}
    (hAₗ : Aₗ ≠ 0) (hBₗ : Bₗ ≠ 0)
    (hAᵣ : Aᵣ ≠ 0) (hBᵣ : Bᵣ ≠ 0)
    (hnarrow : NarrowComplexTurn Aₗ Bₗ Aᵣ Bᵣ) :
    SmallTurnCompatible
      (ofRat Aₗ) (ofRat Bₗ) (ofRat Aᵣ) (ofRat Bᵣ)
      (ofRat (Aₗ * Bᵣ - Bₗ * Aᵣ)) := by
  apply smallTurnCompatible_of_dot_pos hAₗ hBₗ hAᵣ hBᵣ
  unfold NarrowComplexTurn at hnarrow
  exact (mul_nonneg (by norm_num) (abs_nonneg _)).trans_lt hnarrow

end FiniteSign

/-- Four formal factor-coordinate signs; the two product-coordinate signs
are derived conservatively, so complex-product compatibility is automatic. -/
structure ProductCenterSigns where
  factorLeftReal : FiniteSign
  factorLeftImag : FiniteSign
  factorRightReal : FiniteSign
  factorRightImag : FiniteSign
deriving DecidableEq, Repr

namespace ProductCenterSigns

/-- Conservative formal real coordinate of the product center. -/
def productReal (centers : ProductCenterSigns) : FiniteSign :=
  FiniteSign.productRealChoice
    centers.factorLeftReal centers.factorLeftImag
    centers.factorRightReal centers.factorRightImag

/-- Conservative formal imaginary coordinate of the product center. -/
def productImag (centers : ProductCenterSigns) : FiniteSign :=
  FiniteSign.productImagChoice
    centers.factorLeftReal centers.factorLeftImag
    centers.factorRightReal centers.factorRightImag

/-- Pure finite-sign form of coordinated center admissibility. -/
def AdmissibleSigns
    (centers : ProductCenterSigns)
    (Aₗ Bₗ Cₗ Dₗ Eₗ Hₗ Aᵣ Bᵣ Cᵣ Dᵣ Eᵣ Hᵣ : FiniteSign) : Prop :=
  FiniteSign.EventCenterAdmissible
      centers.factorLeftReal centers.factorLeftImag
      Aₗ Bₗ Aᵣ Bᵣ ∧
    FiniteSign.EventCenterAdmissible
      centers.factorRightReal centers.factorRightImag
      Cₗ Dₗ Cᵣ Dᵣ ∧
    FiniteSign.EventCenterAdmissible
      centers.productReal centers.productImag
      Eₗ Hₗ Eᵣ Hᵣ

instance
    (centers : ProductCenterSigns)
    (Aₗ Bₗ Cₗ Dₗ Eₗ Hₗ Aᵣ Bᵣ Cᵣ Dᵣ Eᵣ Hᵣ : FiniteSign) :
    Decidable (centers.AdmissibleSigns
      Aₗ Bₗ Cₗ Dₗ Eₗ Hₗ Aᵣ Bᵣ Cᵣ Dᵣ Eᵣ Hᵣ) := by
  unfold AdmissibleSigns
  infer_instance

open FiniteSign

/-- Direct choice of factor-center signs from the three endpoint transition
shapes.  A coordinate is retained only when the resulting product-center
pair remains stable at both product endpoints. -/
private def coordinatedCenter
    (leftShape rightShape productShape : SmallTurnShape)
    (A B C D : FiniteSign) : ProductCenterSigns :=
  match leftShape, rightShape, productShape with
  | .imagChange, .imagChange, _ => ⟨A, .zero, C, .zero⟩
  | .imagChange, .realChange, _ => ⟨A, .zero, .zero, D⟩
  | .imagChange, .same, .realChange => ⟨A, .zero, .zero, D⟩
  | .imagChange, .same, _ => ⟨A, .zero, C, .zero⟩
  | .realChange, .imagChange, _ => ⟨.zero, B, C, .zero⟩
  | .realChange, .realChange, _ => ⟨.zero, B, .zero, D⟩
  | .realChange, .same, .realChange => ⟨.zero, B, C, .zero⟩
  | .realChange, .same, _ => ⟨.zero, B, .zero, D⟩
  | .same, .imagChange, .realChange => ⟨.zero, B, C, .zero⟩
  | .same, .imagChange, _ => ⟨A, .zero, C, .zero⟩
  | .same, .realChange, .realChange => ⟨A, .zero, .zero, D⟩
  | .same, .realChange, _ => ⟨.zero, B, .zero, D⟩
  | .same, .same, .imagChange => ⟨A, .zero, C, .zero⟩
  | .same, .same, .realChange => ⟨.zero, B, C, .zero⟩
  | .same, .same, .same => ⟨A, B, C, D⟩

private def CoordinatedCenterRow
    (leftShape rightShape productShape : SmallTurnShape)
    (A B C D E H leftTurn rightTurn productTurn : FiniteSign) : Prop :=
    SmallTurnCompatible A B
      (applySmallTurnShape leftShape A B).1
      (applySmallTurnShape leftShape A B).2 leftTurn →
    SmallTurnCompatible C D
      (applySmallTurnShape rightShape C D).1
      (applySmallTurnShape rightShape C D).2 rightTurn →
    SmallTurnCompatible E H
      (applySmallTurnShape productShape E H).1
      (applySmallTurnShape productShape E H).2 productTurn →
    SumCompatible leftTurn rightTurn productTurn →
    ComplexProductCompatible A B C D E H →
    ComplexProductCompatible
      (applySmallTurnShape leftShape A B).1
      (applySmallTurnShape leftShape A B).2
      (applySmallTurnShape rightShape C D).1
      (applySmallTurnShape rightShape C D).2
      (applySmallTurnShape productShape E H).1
      (applySmallTurnShape productShape E H).2 →
    (coordinatedCenter leftShape rightShape productShape A B C D).AdmissibleSigns
      A B C D E H
      (applySmallTurnShape leftShape A B).1
      (applySmallTurnShape leftShape A B).2
      (applySmallTurnShape rightShape C D).1
      (applySmallTurnShape rightShape C D).2
      (applySmallTurnShape productShape E H).1
      (applySmallTurnShape productShape E H).2

private instance
    (leftShape rightShape productShape : SmallTurnShape)
    (A B C D E H leftTurn rightTurn productTurn : FiniteSign) :
    Decidable (CoordinatedCenterRow leftShape rightShape productShape
      A B C D E H leftTurn rightTurn productTurn) := by
  unfold CoordinatedCenterRow
  infer_instance

private def finiteSignOfBool : Bool → FiniteSign
  | false => .negative
  | true => .positive

private def boolOfFiniteSign : FiniteSign → Bool
  | .negative => false
  | .zero => false
  | .positive => true

private theorem finiteSignOfBool_boolOfFiniteSign
    (sign : FiniteSign) (hne : sign ≠ .zero) :
    finiteSignOfBool (boolOfFiniteSign sign) = sign := by
  cases sign <;> simp_all [finiteSignOfBool, boolOfFiniteSign]

private theorem coordinated_strict_same_same :
    ∀ productShape (A B C D E H : Bool) leftTurn rightTurn productTurn,
      CoordinatedCenterRow .same .same productShape
        (finiteSignOfBool A) (finiteSignOfBool B)
        (finiteSignOfBool C) (finiteSignOfBool D)
        (finiteSignOfBool E) (finiteSignOfBool H)
        leftTurn rightTurn productTurn := by
  intro productShape
  cases productShape <;> decide +revert

private theorem coordinated_strict_same_realChange :
    ∀ productShape (A B C D E H : Bool) leftTurn rightTurn productTurn,
      CoordinatedCenterRow .same .realChange productShape
        (finiteSignOfBool A) (finiteSignOfBool B)
        (finiteSignOfBool C) (finiteSignOfBool D)
        (finiteSignOfBool E) (finiteSignOfBool H)
        leftTurn rightTurn productTurn := by
  intro productShape
  cases productShape <;> decide +revert

private theorem coordinated_strict_same_imagChange :
    ∀ productShape (A B C D E H : Bool) leftTurn rightTurn productTurn,
      CoordinatedCenterRow .same .imagChange productShape
        (finiteSignOfBool A) (finiteSignOfBool B)
        (finiteSignOfBool C) (finiteSignOfBool D)
        (finiteSignOfBool E) (finiteSignOfBool H)
        leftTurn rightTurn productTurn := by
  intro productShape
  cases productShape <;> decide +revert

private theorem coordinated_strict_realChange_same :
    ∀ productShape (A B C D E H : Bool) leftTurn rightTurn productTurn,
      CoordinatedCenterRow .realChange .same productShape
        (finiteSignOfBool A) (finiteSignOfBool B)
        (finiteSignOfBool C) (finiteSignOfBool D)
        (finiteSignOfBool E) (finiteSignOfBool H)
        leftTurn rightTurn productTurn := by
  intro productShape
  cases productShape <;> decide +revert

private theorem coordinated_strict_realChange_realChange :
    ∀ productShape (A B C D E H : Bool) leftTurn rightTurn productTurn,
      CoordinatedCenterRow .realChange .realChange productShape
        (finiteSignOfBool A) (finiteSignOfBool B)
        (finiteSignOfBool C) (finiteSignOfBool D)
        (finiteSignOfBool E) (finiteSignOfBool H)
        leftTurn rightTurn productTurn := by
  intro productShape
  cases productShape <;> decide +revert

private theorem coordinated_strict_realChange_imagChange :
    ∀ productShape (A B C D E H : Bool) leftTurn rightTurn productTurn,
      CoordinatedCenterRow .realChange .imagChange productShape
        (finiteSignOfBool A) (finiteSignOfBool B)
        (finiteSignOfBool C) (finiteSignOfBool D)
        (finiteSignOfBool E) (finiteSignOfBool H)
        leftTurn rightTurn productTurn := by
  intro productShape
  cases productShape <;> decide +revert

private theorem coordinated_strict_imagChange_same :
    ∀ productShape (A B C D E H : Bool) leftTurn rightTurn productTurn,
      CoordinatedCenterRow .imagChange .same productShape
        (finiteSignOfBool A) (finiteSignOfBool B)
        (finiteSignOfBool C) (finiteSignOfBool D)
        (finiteSignOfBool E) (finiteSignOfBool H)
        leftTurn rightTurn productTurn := by
  intro productShape
  cases productShape <;> decide +revert

private theorem coordinated_strict_imagChange_realChange :
    ∀ productShape (A B C D E H : Bool) leftTurn rightTurn productTurn,
      CoordinatedCenterRow .imagChange .realChange productShape
        (finiteSignOfBool A) (finiteSignOfBool B)
        (finiteSignOfBool C) (finiteSignOfBool D)
        (finiteSignOfBool E) (finiteSignOfBool H)
        leftTurn rightTurn productTurn := by
  intro productShape
  cases productShape <;> decide +revert

private theorem coordinated_strict_imagChange_imagChange :
    ∀ productShape (A B C D E H : Bool) leftTurn rightTurn productTurn,
      CoordinatedCenterRow .imagChange .imagChange productShape
        (finiteSignOfBool A) (finiteSignOfBool B)
        (finiteSignOfBool C) (finiteSignOfBool D)
        (finiteSignOfBool E) (finiteSignOfBool H)
        leftTurn rightTurn productTurn := by
  intro productShape
  cases productShape <;> decide +revert

private theorem coordinatedCenter_admissible_strict
    (leftShape rightShape productShape : SmallTurnShape)
    (A B C D E H : Bool)
    (leftTurn rightTurn productTurn : FiniteSign) :
    CoordinatedCenterRow leftShape rightShape productShape
      (finiteSignOfBool A) (finiteSignOfBool B)
      (finiteSignOfBool C) (finiteSignOfBool D)
      (finiteSignOfBool E) (finiteSignOfBool H)
      leftTurn rightTurn productTurn := by
  cases leftShape <;> cases rightShape
  · exact coordinated_strict_same_same productShape A B C D E H leftTurn rightTurn productTurn
  · exact coordinated_strict_same_realChange productShape A B C D E H leftTurn rightTurn productTurn
  · exact coordinated_strict_same_imagChange productShape A B C D E H leftTurn rightTurn productTurn
  · exact coordinated_strict_realChange_same productShape A B C D E H leftTurn rightTurn productTurn
  · exact coordinated_strict_realChange_realChange productShape A B C D E H leftTurn rightTurn productTurn
  · exact coordinated_strict_realChange_imagChange productShape A B C D E H leftTurn rightTurn productTurn
  · exact coordinated_strict_imagChange_same productShape A B C D E H leftTurn rightTurn productTurn
  · exact coordinated_strict_imagChange_realChange productShape A B C D E H leftTurn rightTurn productTurn
  · exact coordinated_strict_imagChange_imagChange productShape A B C D E H leftTurn rightTurn productTurn

private theorem coordinatedCenter_admissible
    (leftShape rightShape productShape : SmallTurnShape)
    (A B C D E H leftTurn rightTurn productTurn : FiniteSign) :
    CoordinatedCenterRow leftShape rightShape productShape
      A B C D E H leftTurn rightTurn productTurn := by
  unfold CoordinatedCenterRow
  intro hleft hright hproduct hturn hlower hupper
  have hstrict := coordinatedCenter_admissible_strict
    leftShape rightShape productShape
    (boolOfFiniteSign A) (boolOfFiniteSign B)
    (boolOfFiniteSign C) (boolOfFiniteSign D)
    (boolOfFiniteSign E) (boolOfFiniteSign H)
    leftTurn rightTurn productTurn
  rw [finiteSignOfBool_boolOfFiniteSign A hleft.1,
    finiteSignOfBool_boolOfFiniteSign B hleft.2.1,
    finiteSignOfBool_boolOfFiniteSign C hright.1,
    finiteSignOfBool_boolOfFiniteSign D hright.2.1,
    finiteSignOfBool_boolOfFiniteSign E hproduct.1,
    finiteSignOfBool_boolOfFiniteSign H hproduct.2.1] at hstrict
  exact hstrict hleft hright hproduct hturn hlower hupper


/-- The four proposed factor signs and their two forced product signs are all
nonzero pairs stable against the corresponding rational endpoints. -/
def Admissible
    (centers : ProductCenterSigns)
    (A B C D : RatPolynomial)
    (interval : FTA.SturmTransducer.RationalInterval) : Prop :=
  centers.AdmissibleSigns
    (FiniteSign.ofRat (A.eval interval.lower))
    (FiniteSign.ofRat (B.eval interval.lower))
    (FiniteSign.ofRat (C.eval interval.lower))
    (FiniteSign.ofRat (D.eval interval.lower))
    (FiniteSign.ofRat
      ((productNumerator A B C D).eval interval.lower))
    (FiniteSign.ofRat
      ((productDenominator A B C D).eval interval.lower))
    (FiniteSign.ofRat (A.eval interval.upper))
    (FiniteSign.ofRat (B.eval interval.upper))
    (FiniteSign.ofRat (C.eval interval.upper))
    (FiniteSign.ofRat (D.eval interval.upper))
    (FiniteSign.ofRat
      ((productNumerator A B C D).eval interval.upper))
    (FiniteSign.ofRat
      ((productDenominator A B C D).eval interval.upper))

instance
    (centers : ProductCenterSigns)
    (A B C D : RatPolynomial)
    (interval : FTA.SturmTransducer.RationalInterval) :
    Decidable (centers.Admissible A B C D interval) := by
  unfold Admissible
  infer_instance

/-- Decidable checker for one proposed coordinated center. -/
def check
    (A B C D : RatPolynomial)
    (interval : FTA.SturmTransducer.RationalInterval)
    (centers : ProductCenterSigns) : Bool :=
  decide (centers.Admissible A B C D interval)

theorem admissible_of_check
    {A B C D : RatPolynomial}
    {interval : FTA.SturmTransducer.RationalInterval}
    {centers : ProductCenterSigns}
    (hcheck : check A B C D interval centers = true) :
    centers.Admissible A B C D interval := by
  change decide (centers.Admissible A B C D interval) = true at hcheck
  exact of_decide_eq_true hcheck

/-- Canonical executable enumeration of the `3^4 = 81` possible factor
centers. -/
def candidates : List ProductCenterSigns :=
  finiteSignCandidates.flatMap fun factorLeftReal =>
  finiteSignCandidates.flatMap fun factorLeftImag =>
  finiteSignCandidates.flatMap fun factorRightReal =>
  finiteSignCandidates.map fun factorRightImag =>
    { factorLeftReal, factorLeftImag, factorRightReal, factorRightImag }

theorem mem_candidates (centers : ProductCenterSigns) :
    centers ∈ candidates := by
  rcases centers with
    ⟨factorLeftReal, factorLeftImag, factorRightReal, factorRightImag⟩
  simp only [candidates, List.mem_flatMap, List.mem_map]
  exact ⟨factorLeftReal, mem_finiteSignCandidates factorLeftReal,
    factorLeftImag, mem_finiteSignCandidates factorLeftImag,
    factorRightReal, mem_finiteSignCandidates factorRightReal,
    factorRightImag, mem_finiteSignCandidates factorRightImag, rfl⟩

/-- Finite checker and exhaustive search used by the quadrant-turn table. -/
def signCheck
    (Aₗ Bₗ Cₗ Dₗ Eₗ Hₗ Aᵣ Bᵣ Cᵣ Dᵣ Eᵣ Hᵣ : FiniteSign)
    (centers : ProductCenterSigns) : Bool :=
  decide (centers.AdmissibleSigns
    Aₗ Bₗ Cₗ Dₗ Eₗ Hₗ Aᵣ Bᵣ Cᵣ Dᵣ Eᵣ Hᵣ)

def signSearch?
    (Aₗ Bₗ Cₗ Dₗ Eₗ Hₗ Aᵣ Bᵣ Cᵣ Dᵣ Eᵣ Hᵣ : FiniteSign) :
    Option ProductCenterSigns :=
  candidates.find? fun centers =>
    signCheck Aₗ Bₗ Cₗ Dₗ Eₗ Hₗ Aᵣ Bᵣ Cᵣ Dᵣ Eᵣ Hᵣ centers

theorem signSearch?_some_admissible
    {Aₗ Bₗ Cₗ Dₗ Eₗ Hₗ Aᵣ Bᵣ Cᵣ Dᵣ Eᵣ Hᵣ : FiniteSign}
    {centers : ProductCenterSigns}
    (hsearch : signSearch?
      Aₗ Bₗ Cₗ Dₗ Eₗ Hₗ Aᵣ Bᵣ Cᵣ Dᵣ Eᵣ Hᵣ = some centers) :
    centers.AdmissibleSigns
      Aₗ Bₗ Cₗ Dₗ Eₗ Hₗ Aᵣ Bᵣ Cᵣ Dᵣ Eᵣ Hᵣ := by
  have hcheck := List.find?_some hsearch
  change decide (centers.AdmissibleSigns
    Aₗ Bₗ Cₗ Dₗ Eₗ Hₗ Aᵣ Bᵣ Cᵣ Dᵣ Eᵣ Hᵣ) = true at hcheck
  exact of_decide_eq_true hcheck

/-- Compatible small turns admit an explicit coordinated center.  Endpoint
signs are first classified by which coordinate changes; the resulting
`3 × 3 × 3` shape table selects a center directly, without searching the
81 possible four-sign records or introducing a native-computation axiom. -/
theorem exists_admissibleSigns_of_smallTurns
    (Aₗ Bₗ Cₗ Dₗ Eₗ Hₗ Aᵣ Bᵣ Cᵣ Dᵣ Eᵣ Hᵣ
      leftTurn rightTurn productTurn : FiniteSign)
    (hleft : FiniteSign.SmallTurnCompatible
      Aₗ Bₗ Aᵣ Bᵣ leftTurn)
    (hright : FiniteSign.SmallTurnCompatible
      Cₗ Dₗ Cᵣ Dᵣ rightTurn)
    (hproduct : FiniteSign.SmallTurnCompatible
      Eₗ Hₗ Eᵣ Hᵣ productTurn)
    (hturn : FiniteSign.SumCompatible
      leftTurn rightTurn productTurn)
    (hlower : FiniteSign.ComplexProductCompatible
      Aₗ Bₗ Cₗ Dₗ Eₗ Hₗ)
    (hupper : FiniteSign.ComplexProductCompatible
      Aᵣ Bᵣ Cᵣ Dᵣ Eᵣ Hᵣ) :
    ∃ centers : ProductCenterSigns,
      centers.AdmissibleSigns
        Aₗ Bₗ Cₗ Dₗ Eₗ Hₗ Aᵣ Bᵣ Cᵣ Dᵣ Eᵣ Hᵣ := by
  let leftShape := FiniteSign.smallTurnShape Aₗ Bₗ Aᵣ Bᵣ
  let rightShape := FiniteSign.smallTurnShape Cₗ Dₗ Cᵣ Dᵣ
  let productShape := FiniteSign.smallTurnShape Eₗ Hₗ Eᵣ Hᵣ
  have hleftEndpoints :=
    FiniteSign.apply_smallTurnShape_eq_of_compatible _ _ _ _ _ hleft
  have hrightEndpoints :=
    FiniteSign.apply_smallTurnShape_eq_of_compatible _ _ _ _ _ hright
  have hproductEndpoints :=
    FiniteSign.apply_smallTurnShape_eq_of_compatible _ _ _ _ _ hproduct
  have hleftAtShape : FiniteSign.SmallTurnCompatible Aₗ Bₗ
      (FiniteSign.applySmallTurnShape leftShape Aₗ Bₗ).1
      (FiniteSign.applySmallTurnShape leftShape Aₗ Bₗ).2 leftTurn := by
    rw [hleftEndpoints]
    exact hleft
  have hrightAtShape : FiniteSign.SmallTurnCompatible Cₗ Dₗ
      (FiniteSign.applySmallTurnShape rightShape Cₗ Dₗ).1
      (FiniteSign.applySmallTurnShape rightShape Cₗ Dₗ).2 rightTurn := by
    rw [hrightEndpoints]
    exact hright
  have hproductAtShape : FiniteSign.SmallTurnCompatible Eₗ Hₗ
      (FiniteSign.applySmallTurnShape productShape Eₗ Hₗ).1
      (FiniteSign.applySmallTurnShape productShape Eₗ Hₗ).2 productTurn := by
    rw [hproductEndpoints]
    exact hproduct
  refine ⟨coordinatedCenter leftShape rightShape productShape Aₗ Bₗ Cₗ Dₗ, ?_⟩
  have hadmissible := coordinatedCenter_admissible
    leftShape rightShape productShape Aₗ Bₗ Cₗ Dₗ Eₗ Hₗ
    leftTurn rightTurn productTurn hleftAtShape hrightAtShape
      hproductAtShape hturn hlower (by
        rw [hleftEndpoints, hrightEndpoints, hproductEndpoints]
        exact hupper)
  rw [hleftEndpoints, hrightEndpoints, hproductEndpoints] at hadmissible
  exact hadmissible

/-- Rational specialization of the finite quadrant-turn table.  Two narrow
factor turns make the product dot positive, their oriented cross signs add,
and the exact endpoint multiplication identities supply a coordinated
formal center without naming an intermediate zero. -/
theorem exists_admissibleSigns_of_narrowTurns
    {Aₗ Bₗ Cₗ Dₗ Aᵣ Bᵣ Cᵣ Dᵣ : ℚ}
    (hAₗ : Aₗ ≠ 0) (hBₗ : Bₗ ≠ 0)
    (hCₗ : Cₗ ≠ 0) (hDₗ : Dₗ ≠ 0)
    (hEₗ : Aₗ * Cₗ - Bₗ * Dₗ ≠ 0)
    (hHₗ : Aₗ * Dₗ + Bₗ * Cₗ ≠ 0)
    (hAᵣ : Aᵣ ≠ 0) (hBᵣ : Bᵣ ≠ 0)
    (hCᵣ : Cᵣ ≠ 0) (hDᵣ : Dᵣ ≠ 0)
    (hEᵣ : Aᵣ * Cᵣ - Bᵣ * Dᵣ ≠ 0)
    (hHᵣ : Aᵣ * Dᵣ + Bᵣ * Cᵣ ≠ 0)
    (hleft : NarrowComplexTurn Aₗ Bₗ Aᵣ Bᵣ)
    (hright : NarrowComplexTurn Cₗ Dₗ Cᵣ Dᵣ) :
    ∃ centers : ProductCenterSigns,
      centers.AdmissibleSigns
        (FiniteSign.ofRat Aₗ) (FiniteSign.ofRat Bₗ)
        (FiniteSign.ofRat Cₗ) (FiniteSign.ofRat Dₗ)
        (FiniteSign.ofRat (Aₗ * Cₗ - Bₗ * Dₗ))
        (FiniteSign.ofRat (Aₗ * Dₗ + Bₗ * Cₗ))
        (FiniteSign.ofRat Aᵣ) (FiniteSign.ofRat Bᵣ)
        (FiniteSign.ofRat Cᵣ) (FiniteSign.ofRat Dᵣ)
        (FiniteSign.ofRat (Aᵣ * Cᵣ - Bᵣ * Dᵣ))
        (FiniteSign.ofRat (Aᵣ * Dᵣ + Bᵣ * Cᵣ)) := by
  let Eₗ := Aₗ * Cₗ - Bₗ * Dₗ
  let Hₗ := Aₗ * Dₗ + Bₗ * Cₗ
  let Eᵣ := Aᵣ * Cᵣ - Bᵣ * Dᵣ
  let Hᵣ := Aᵣ * Dᵣ + Bᵣ * Cᵣ
  let leftTurn := FiniteSign.ofRat (Aₗ * Bᵣ - Bₗ * Aᵣ)
  let rightTurn := FiniteSign.ofRat (Cₗ * Dᵣ - Dₗ * Cᵣ)
  let productTurn := FiniteSign.ofRat (Eₗ * Hᵣ - Hₗ * Eᵣ)
  have hleftSmall : FiniteSign.SmallTurnCompatible
      (FiniteSign.ofRat Aₗ) (FiniteSign.ofRat Bₗ)
      (FiniteSign.ofRat Aᵣ) (FiniteSign.ofRat Bᵣ) leftTurn := by
    simpa only [leftTurn] using
      FiniteSign.smallTurnCompatible_of_narrowComplexTurn
        hAₗ hBₗ hAᵣ hBᵣ hleft
  have hrightSmall : FiniteSign.SmallTurnCompatible
      (FiniteSign.ofRat Cₗ) (FiniteSign.ofRat Dₗ)
      (FiniteSign.ofRat Cᵣ) (FiniteSign.ofRat Dᵣ) rightTurn := by
    simpa only [rightTurn] using
      FiniteSign.smallTurnCompatible_of_narrowComplexTurn
        hCₗ hDₗ hCᵣ hDᵣ hright
  have hproductDot : 0 < Eₗ * Eᵣ + Hₗ * Hᵣ := by
    simpa only [Eₗ, Hₗ, Eᵣ, Hᵣ] using
      productComplexDot_pos_of_narrowTurns hleft hright
  have hproductSmall : FiniteSign.SmallTurnCompatible
      (FiniteSign.ofRat Eₗ) (FiniteSign.ofRat Hₗ)
      (FiniteSign.ofRat Eᵣ) (FiniteSign.ofRat Hᵣ) productTurn := by
    apply FiniteSign.smallTurnCompatible_of_dot_pos
      (by simpa only [Eₗ] using hEₗ)
      (by simpa only [Hₗ] using hHₗ)
      (by simpa only [Eᵣ] using hEᵣ)
      (by simpa only [Hᵣ] using hHᵣ)
    exact hproductDot
  have hturn : FiniteSign.SumCompatible
      leftTurn rightTurn productTurn := by
    simpa only [leftTurn, rightTurn, productTurn, Eₗ, Hₗ, Eᵣ, Hᵣ] using
      productTurn_sumCompatible_of_narrowTurns hleft hright
  have hlower : FiniteSign.ComplexProductCompatible
      (FiniteSign.ofRat Aₗ) (FiniteSign.ofRat Bₗ)
      (FiniteSign.ofRat Cₗ) (FiniteSign.ofRat Dₗ)
      (FiniteSign.ofRat Eₗ) (FiniteSign.ofRat Hₗ) := by
    simpa only [Eₗ, Hₗ] using
      finiteSign_complexProductCompatible Aₗ Bₗ Cₗ Dₗ
  have hupper : FiniteSign.ComplexProductCompatible
      (FiniteSign.ofRat Aᵣ) (FiniteSign.ofRat Bᵣ)
      (FiniteSign.ofRat Cᵣ) (FiniteSign.ofRat Dᵣ)
      (FiniteSign.ofRat Eᵣ) (FiniteSign.ofRat Hᵣ) := by
    simpa only [Eᵣ, Hᵣ] using
      finiteSign_complexProductCompatible Aᵣ Bᵣ Cᵣ Dᵣ
  simpa only [Eₗ, Hₗ, Eᵣ, Hᵣ] using
    exists_admissibleSigns_of_smallTurns
      (FiniteSign.ofRat Aₗ) (FiniteSign.ofRat Bₗ)
      (FiniteSign.ofRat Cₗ) (FiniteSign.ofRat Dₗ)
      (FiniteSign.ofRat Eₗ) (FiniteSign.ofRat Hₗ)
      (FiniteSign.ofRat Aᵣ) (FiniteSign.ofRat Bᵣ)
      (FiniteSign.ofRat Cᵣ) (FiniteSign.ofRat Dᵣ)
      (FiniteSign.ofRat Eᵣ) (FiniteSign.ofRat Hᵣ)
      leftTurn rightTurn productTurn hleftSmall hrightSmall hproductSmall
      hturn hlower hupper

/-- Exhaustive executable search for factor centers whose conservative
formal product center is also endpoint-admissible. -/
def search?
    (A B C D : RatPolynomial)
    (interval : FTA.SturmTransducer.RationalInterval) :
    Option ProductCenterSigns :=
  candidates.find? fun centers => check A B C D interval centers

theorem search?_some_admissible
    {A B C D : RatPolynomial}
    {interval : FTA.SturmTransducer.RationalInterval}
    {centers : ProductCenterSigns}
    (hsearch : search? A B C D interval = some centers) :
    centers.Admissible A B C D interval := by
  apply admissible_of_check
  exact List.find?_some hsearch

/-- Exhaustiveness of the finite coordinated-center search. -/
theorem search?_isSome_of_admissible
    {A B C D : RatPolynomial}
    {interval : FTA.SturmTransducer.RationalInterval}
    (centers : ProductCenterSigns)
    (hadmissible : centers.Admissible A B C D interval) :
    (search? A B C D interval).isSome := by
  rw [search?, List.find?_isSome]
  refine ⟨centers, mem_candidates centers, ?_⟩
  simp [check, hadmissible]

/-- On a cell where all six coordinate endpoints are clear, narrow turns of
the two factor vectors make the executable coordinated-center search
succeed. -/
theorem search?_isSome_of_narrowTurns
    {A B C D : RatPolynomial}
    {interval : FTA.SturmTransducer.RationalInterval}
    (hAₗ : A.eval interval.lower ≠ 0)
    (hBₗ : B.eval interval.lower ≠ 0)
    (hCₗ : C.eval interval.lower ≠ 0)
    (hDₗ : D.eval interval.lower ≠ 0)
    (hEₗ : (productNumerator A B C D).eval interval.lower ≠ 0)
    (hHₗ : (productDenominator A B C D).eval interval.lower ≠ 0)
    (hAᵣ : A.eval interval.upper ≠ 0)
    (hBᵣ : B.eval interval.upper ≠ 0)
    (hCᵣ : C.eval interval.upper ≠ 0)
    (hDᵣ : D.eval interval.upper ≠ 0)
    (hEᵣ : (productNumerator A B C D).eval interval.upper ≠ 0)
    (hHᵣ : (productDenominator A B C D).eval interval.upper ≠ 0)
    (hleft : NarrowComplexTurn
      (A.eval interval.lower) (B.eval interval.lower)
      (A.eval interval.upper) (B.eval interval.upper))
    (hright : NarrowComplexTurn
      (C.eval interval.lower) (D.eval interval.lower)
      (C.eval interval.upper) (D.eval interval.upper)) :
    (search? A B C D interval).isSome := by
  rcases exists_admissibleSigns_of_narrowTurns
      hAₗ hBₗ hCₗ hDₗ
      (by simpa only [eval_productNumerator] using hEₗ)
      (by simpa only [eval_productDenominator] using hHₗ)
      hAᵣ hBᵣ hCᵣ hDᵣ
      (by simpa only [eval_productNumerator] using hEᵣ)
      (by simpa only [eval_productDenominator] using hHᵣ)
      hleft hright with ⟨centers, hadmissible⟩
  apply search?_isSome_of_admissible centers
  simpa only [Admissible, eval_productNumerator,
    eval_productDenominator] using hadmissible

/-- One positive coefficient width forcing narrow turns for both coprime
factor pairs. -/
def turnWidthResolution
    {A B C D : RatPolynomial}
    (left : FTA.DenseSquarefree.CoprimeCertificate A B)
    (right : FTA.DenseSquarefree.CoprimeCertificate C D)
    (root : FTA.SturmTransducer.RationalInterval) : ℚ :=
  min (coprimeNarrowTurnWidthResolution left root)
    (coprimeNarrowTurnWidthResolution right root)

theorem turnWidthResolution_pos
    {A B C D : RatPolynomial}
    (left : FTA.DenseSquarefree.CoprimeCertificate A B)
    (right : FTA.DenseSquarefree.CoprimeCertificate C D)
    (root : FTA.SturmTransducer.RationalInterval) :
    0 < turnWidthResolution left right root := by
  apply lt_min
  · exact coprimeNarrowTurnWidthResolution_pos left root
  · exact coprimeNarrowTurnWidthResolution_pos right root

/-- The coefficient-computed turn width discharges the entire coordinated
center search on every clear nested cell. -/
theorem search?_isSome_of_refined_width
    {A B C D : RatPolynomial}
    (left : FTA.DenseSquarefree.CoprimeCertificate A B)
    (right : FTA.DenseSquarefree.CoprimeCertificate C D)
    (root interval : FTA.SturmTransducer.RationalInterval)
    (hrefines : interval.Refines root) (proper : interval.Proper)
    (hwidth : interval.width < turnWidthResolution left right root)
    (hAₗ : A.eval interval.lower ≠ 0)
    (hBₗ : B.eval interval.lower ≠ 0)
    (hCₗ : C.eval interval.lower ≠ 0)
    (hDₗ : D.eval interval.lower ≠ 0)
    (hEₗ : (productNumerator A B C D).eval interval.lower ≠ 0)
    (hHₗ : (productDenominator A B C D).eval interval.lower ≠ 0)
    (hAᵣ : A.eval interval.upper ≠ 0)
    (hBᵣ : B.eval interval.upper ≠ 0)
    (hCᵣ : C.eval interval.upper ≠ 0)
    (hDᵣ : D.eval interval.upper ≠ 0)
    (hEᵣ : (productNumerator A B C D).eval interval.upper ≠ 0)
    (hHᵣ : (productDenominator A B C D).eval interval.upper ≠ 0) :
    (search? A B C D interval).isSome := by
  apply search?_isSome_of_narrowTurns
    hAₗ hBₗ hCₗ hDₗ hEₗ hHₗ hAᵣ hBᵣ hCᵣ hDᵣ hEᵣ hHᵣ
  · apply narrowComplexTurn_of_coprime_refined_width
      left root interval hrefines proper
    exact hwidth.trans_le (by
      dsimp only [turnWidthResolution]
      exact min_le_left _ _)
  · apply narrowComplexTurn_of_coprime_refined_width
      right root interval hrefines proper
    exact hwidth.trans_le (by
      dsimp only [turnWidthResolution]
      exact min_le_right _ _)

end ProductCenterSigns

/-- Three exact Cauchy records whose formal centers already satisfy complex
multiplication. -/
structure CompatibleCauchyEventTriple
    (A B C D : RatPolynomial)
    (interval : FTA.SturmTransducer.RationalInterval) where
  left : CauchyEventSigns A B interval
  right : CauchyEventSigns C D interval
  product : CauchyEventSigns (productNumerator A B C D)
    (productDenominator A B C D) interval
  compatible : FiniteSign.ComplexProductCompatible
    left.numerator left.denominator right.numerator right.denominator
    product.numerator product.denominator

namespace CompatibleCauchyEventTriple

/-- Coordinate three precomputed records by re-centering the factor pairs
and choosing the conservative forced signs of their formal complex product.
Only endpoint stability of those six new signs remains to be supplied; all
three exact chain indices are inherited automatically. -/
def ofRecenteredFactors
    {A B C D : RatPolynomial}
    {interval : FTA.SturmTransducer.RationalInterval}
    (leftBase : CauchyEventSigns A B interval)
    (rightBase : CauchyEventSigns C D interval)
    (productBase : CauchyEventSigns (productNumerator A B C D)
      (productDenominator A B C D) interval)
    (factorLeftReal factorLeftImag factorRightReal factorRightImag :
      FiniteSign)
    (leftCenter : FiniteSign.EventCenterAdmissible
      factorLeftReal factorLeftImag
      (FiniteSign.ofRat (A.eval interval.lower))
      (FiniteSign.ofRat (B.eval interval.lower))
      (FiniteSign.ofRat (A.eval interval.upper))
      (FiniteSign.ofRat (B.eval interval.upper)))
    (rightCenter : FiniteSign.EventCenterAdmissible
      factorRightReal factorRightImag
      (FiniteSign.ofRat (C.eval interval.lower))
      (FiniteSign.ofRat (D.eval interval.lower))
      (FiniteSign.ofRat (C.eval interval.upper))
      (FiniteSign.ofRat (D.eval interval.upper)))
    (productCenter : FiniteSign.EventCenterAdmissible
      (FiniteSign.productRealChoice factorLeftReal factorLeftImag
        factorRightReal factorRightImag)
      (FiniteSign.productImagChoice factorLeftReal factorLeftImag
        factorRightReal factorRightImag)
      (FiniteSign.ofRat
        ((productNumerator A B C D).eval interval.lower))
      (FiniteSign.ofRat
        ((productDenominator A B C D).eval interval.lower))
      (FiniteSign.ofRat
        ((productNumerator A B C D).eval interval.upper))
      (FiniteSign.ofRat
        ((productDenominator A B C D).eval interval.upper))) :
    CompatibleCauchyEventTriple A B C D interval := by
  rcases leftCenter with
    ⟨leftNonzero, leftRealLower, leftImagLower,
      leftRealUpper, leftImagUpper⟩
  rcases rightCenter with
    ⟨rightNonzero, rightRealLower, rightImagLower,
      rightRealUpper, rightImagUpper⟩
  rcases productCenter with
    ⟨productNonzero, productRealLower, productImagLower,
      productRealUpper, productImagUpper⟩
  let left := leftBase.recenter factorLeftReal factorLeftImag
    leftNonzero leftRealLower leftImagLower leftRealUpper leftImagUpper
  let right := rightBase.recenter factorRightReal factorRightImag
    rightNonzero rightRealLower rightImagLower rightRealUpper rightImagUpper
  let product := productBase.recenter
    (FiniteSign.productRealChoice factorLeftReal factorLeftImag
      factorRightReal factorRightImag)
    (FiniteSign.productImagChoice factorLeftReal factorLeftImag
      factorRightReal factorRightImag)
    productNonzero productRealLower productImagLower
    productRealUpper productImagUpper
  exact
    { left := left
      right := right
      product := product
      compatible := by
        simpa only [left, right, product, CauchyEventSigns.recenter] using
          FiniteSign.productChoices_compatible
            factorLeftReal factorLeftImag factorRightReal factorRightImag }

/-- Turn one successful four-sign center candidate into a coordinated triple
without repeating any endpoint-stability bookkeeping. -/
def ofCenters
    {A B C D : RatPolynomial}
    {interval : FTA.SturmTransducer.RationalInterval}
    (leftBase : CauchyEventSigns A B interval)
    (rightBase : CauchyEventSigns C D interval)
    (productBase : CauchyEventSigns (productNumerator A B C D)
      (productDenominator A B C D) interval)
    (centers : ProductCenterSigns)
    (hadmissible : centers.Admissible A B C D interval) :
    CompatibleCauchyEventTriple A B C D interval :=
  ofRecenteredFactors leftBase rightBase productBase
    centers.factorLeftReal centers.factorLeftImag
    centers.factorRightReal centers.factorRightImag
    hadmissible.1 hadmissible.2.1 hadmissible.2.2

/-- Proof-bearing executable center coordination.  Failure now means exactly
that none of the 81 four-sign candidates passes the endpoint checker. -/
def search?
    {A B C D : RatPolynomial}
    {interval : FTA.SturmTransducer.RationalInterval}
    (leftBase : CauchyEventSigns A B interval)
    (rightBase : CauchyEventSigns C D interval)
    (productBase : CauchyEventSigns (productNumerator A B C D)
      (productDenominator A B C D) interval) :
    Option (CompatibleCauchyEventTriple A B C D interval) :=
  match hsearch : ProductCenterSigns.search? A B C D interval with
  | none => none
  | some centers => some <|
      ofCenters leftBase rightBase productBase centers
        (ProductCenterSigns.search?_some_admissible hsearch)

theorem search?_isSome
    {A B C D : RatPolynomial}
    {interval : FTA.SturmTransducer.RationalInterval}
    (leftBase : CauchyEventSigns A B interval)
    (rightBase : CauchyEventSigns C D interval)
    (productBase : CauchyEventSigns (productNumerator A B C D)
      (productDenominator A B C D) interval) :
    (search? leftBase rightBase productBase).isSome =
      (ProductCenterSigns.search? A B C D interval).isSome := by
  unfold search?
  split <;> rename_i hsearch <;>
    simp only [hsearch, Option.isSome_none, Option.isSome_some]

/-- The same coefficient turn width makes the proof-bearing triple search
succeed once the three exact Cauchy records have been computed. -/
theorem search?_isSome_of_refined_width
    {A B C D : RatPolynomial}
    {interval : FTA.SturmTransducer.RationalInterval}
    (leftBase : CauchyEventSigns A B interval)
    (rightBase : CauchyEventSigns C D interval)
    (productBase : CauchyEventSigns (productNumerator A B C D)
      (productDenominator A B C D) interval)
    (left : FTA.DenseSquarefree.CoprimeCertificate A B)
    (right : FTA.DenseSquarefree.CoprimeCertificate C D)
    (root : FTA.SturmTransducer.RationalInterval)
    (hrefines : interval.Refines root) (proper : interval.Proper)
    (hwidth : interval.width <
      ProductCenterSigns.turnWidthResolution left right root)
    (hAₗ : A.eval interval.lower ≠ 0)
    (hBₗ : B.eval interval.lower ≠ 0)
    (hCₗ : C.eval interval.lower ≠ 0)
    (hDₗ : D.eval interval.lower ≠ 0)
    (hEₗ : (productNumerator A B C D).eval interval.lower ≠ 0)
    (hHₗ : (productDenominator A B C D).eval interval.lower ≠ 0)
    (hAᵣ : A.eval interval.upper ≠ 0)
    (hBᵣ : B.eval interval.upper ≠ 0)
    (hCᵣ : C.eval interval.upper ≠ 0)
    (hDᵣ : D.eval interval.upper ≠ 0)
    (hEᵣ : (productNumerator A B C D).eval interval.upper ≠ 0)
    (hHᵣ : (productDenominator A B C D).eval interval.upper ≠ 0) :
    (search? leftBase rightBase productBase).isSome := by
  rw [search?_isSome]
  exact ProductCenterSigns.search?_isSome_of_refined_width
    left right root interval hrefines proper hwidth
    hAₗ hBₗ hCₗ hDₗ hEₗ hHₗ hAᵣ hBᵣ hCᵣ hDᵣ hEᵣ hHᵣ

end CompatibleCauchyEventTriple

/-- Lift a reduced-coordinate event record through a common polynomial factor
whose sign is coefficient-resolved on the cell.  The factor need not be
constant, which is essential for product coordinates that acquire a
root-free nonconstant gcd. -/
def ReducedCauchyEventSigns.ofResolvedCommonFactor
    {R S : RatPolynomial}
    {interval : FTA.SturmTransducer.RationalInterval}
    (data : ReducedCauchyEventSigns R S interval)
    (proper : interval.Proper)
    (resolved : FTA.SturmTransducer.MidpointResolved interval
      (FTA.DenseGCD.symmetricGCD R S)) :
    CauchyEventSigns R S interval := by
  let g := FTA.DenseGCD.symmetricGCD R S
  let k := FiniteSign.ofRat (g.eval interval.lower)
  have hgEndpoints :=
    FTA.SturmTransducer.eval_lower_mul_eval_upper_pos_of_midpointResolved
      interval proper g (by simpa only [g] using resolved)
  have hgLower : g.eval interval.lower ≠ 0 :=
    left_ne_zero_of_mul hgEndpoints.ne'
  have hk : k ≠ .zero := by
    simpa [k, FiniteSign.ofRat_eq_zero_iff] using hgLower
  have hgStable : FiniteSign.Stable k
      (FiniteSign.ofRat (g.eval interval.upper)) :=
    finiteSign_stable_of_eq_zero_or_mul_pos (Or.inr hgEndpoints)
  have hgSignEq : k = FiniteSign.ofRat (g.eval interval.upper) := by
    rcases hgStable with hzero | heq
    · exact (hk hzero).elim
    · exact heq
  have hRLower : FiniteSign.ofRat (R.eval interval.lower) =
      FiniteSign.mul k
        (FiniteSign.ofRat ((reducedNumerator R S).eval interval.lower)) := by
    rw [FTA.DenseGCD.symmetricLeftFactor_eval_identity R S,
      FiniteSign.ofRat_mul]
    rfl
  have hSLower : FiniteSign.ofRat (S.eval interval.lower) =
      FiniteSign.mul k
        (FiniteSign.ofRat ((reducedDenominator R S).eval interval.lower)) := by
    rw [FTA.DenseGCD.symmetricRightFactor_eval_identity R S,
      FiniteSign.ofRat_mul]
    rfl
  have hRUpper : FiniteSign.ofRat (R.eval interval.upper) =
      FiniteSign.mul k
        (FiniteSign.ofRat ((reducedNumerator R S).eval interval.upper)) := by
    rw [FTA.DenseGCD.symmetricLeftFactor_eval_identity R S,
      FiniteSign.ofRat_mul]
    change FiniteSign.mul (FiniteSign.ofRat (g.eval interval.upper))
        (FiniteSign.ofRat ((reducedNumerator R S).eval interval.upper)) = _
    rw [← hgSignEq]
  have hSUpper : FiniteSign.ofRat (S.eval interval.upper) =
      FiniteSign.mul k
        (FiniteSign.ofRat ((reducedDenominator R S).eval interval.upper)) := by
    rw [FTA.DenseGCD.symmetricRightFactor_eval_identity R S,
      FiniteSign.ofRat_mul]
    change FiniteSign.mul (FiniteSign.ofRat (g.eval interval.upper))
        (FiniteSign.ofRat ((reducedDenominator R S).eval interval.upper)) = _
    rw [← hgSignEq]
  refine
    { numerator := FiniteSign.mul k data.numerator
      denominator := FiniteSign.mul k data.denominator
      nonzero := ?_
      numeratorLowerStable := ?_
      denominatorLowerStable := ?_
      numeratorUpperStable := ?_
      denominatorUpperStable := ?_
      index := ?_ }
  · rcases data.nonzero with hn | hd
    · exact Or.inl (FiniteSign.mul_ne_zero hk hn)
    · exact Or.inr (FiniteSign.mul_ne_zero hk hd)
  · rw [hRLower]
    exact FiniteSign.stable_mul_left k _ _ data.numeratorLowerStable
  · rw [hSLower]
    exact FiniteSign.stable_mul_left k _ _ data.denominatorLowerStable
  · rw [hRUpper]
    exact FiniteSign.stable_mul_left k _ _ data.numeratorUpperStable
  · rw [hSUpper]
    exact FiniteSign.stable_mul_left k _ _ data.denominatorUpperStable
  · rw [data.index, hRLower, hSLower, hRUpper, hSUpper]
    exact (FiniteSign.eventIndex2_mul_left k data.numerator data.denominator
      (FiniteSign.ofRat ((reducedNumerator R S).eval interval.lower))
      (FiniteSign.ofRat ((reducedDenominator R S).eval interval.lower))
      (FiniteSign.ofRat ((reducedNumerator R S).eval interval.upper))
      (FiniteSign.ofRat ((reducedDenominator R S).eval interval.upper)) hk).symm

/-- Lift a computed reduced-coordinate event record through the unique common
nonzero scalar relating any coprime input pair to its canonical reduction. -/
def ReducedCauchyEventSigns.ofCoprime
    {R S : RatPolynomial}
    {interval : FTA.SturmTransducer.RationalInterval}
    (data : ReducedCauchyEventSigns R S interval)
    (coprime : FTA.DenseSquarefree.CoprimeCertificate R S) :
    CauchyEventSigns R S interval := by
  let scaleData := coprimePairReductionScale R S coprime
  let c := scaleData.scalar
  have hc : c ≠ 0 := scaleData.nonzero
  have hRScale := scaleData.numeratorEval
  have hSScale := scaleData.denominatorEval
  let k := FiniteSign.ofRat c
  have hk : k ≠ .zero := by
    simpa [k, FiniteSign.ofRat_eq_zero_iff] using hc
  have hRLower : FiniteSign.ofRat (R.eval interval.lower) =
      FiniteSign.mul k
        (FiniteSign.ofRat ((reducedNumerator R S).eval interval.lower)) := by
    rw [hRScale, FiniteSign.ofRat_mul]
  have hSLower : FiniteSign.ofRat (S.eval interval.lower) =
      FiniteSign.mul k
        (FiniteSign.ofRat ((reducedDenominator R S).eval interval.lower)) := by
    rw [hSScale, FiniteSign.ofRat_mul]
  have hRUpper : FiniteSign.ofRat (R.eval interval.upper) =
      FiniteSign.mul k
        (FiniteSign.ofRat ((reducedNumerator R S).eval interval.upper)) := by
    rw [hRScale, FiniteSign.ofRat_mul]
  have hSUpper : FiniteSign.ofRat (S.eval interval.upper) =
      FiniteSign.mul k
        (FiniteSign.ofRat ((reducedDenominator R S).eval interval.upper)) := by
    rw [hSScale, FiniteSign.ofRat_mul]
  refine
    { numerator := FiniteSign.mul k data.numerator
      denominator := FiniteSign.mul k data.denominator
      nonzero := ?_
      numeratorLowerStable := ?_
      denominatorLowerStable := ?_
      numeratorUpperStable := ?_
      denominatorUpperStable := ?_
      index := ?_ }
  · rcases data.nonzero with hn | hd
    · exact Or.inl (FiniteSign.mul_ne_zero hk hn)
    · exact Or.inr (FiniteSign.mul_ne_zero hk hd)
  · rw [hRLower]
    exact FiniteSign.stable_mul_left k _ _ data.numeratorLowerStable
  · rw [hSLower]
    exact FiniteSign.stable_mul_left k _ _ data.denominatorLowerStable
  · rw [hRUpper]
    exact FiniteSign.stable_mul_left k _ _ data.numeratorUpperStable
  · rw [hSUpper]
    exact FiniteSign.stable_mul_left k _ _ data.denominatorUpperStable
  · rw [data.index, hRLower, hSLower, hRUpper, hSUpper]
    exact (FiniteSign.eventIndex2_mul_left k data.numerator data.denominator
      (FiniteSign.ofRat ((reducedNumerator R S).eval interval.lower))
      (FiniteSign.ofRat ((reducedDenominator R S).eval interval.lower))
      (FiniteSign.ofRat ((reducedNumerator R S).eval interval.upper))
      (FiniteSign.ofRat ((reducedDenominator R S).eval interval.upper)) hk).symm

/-- End-to-end coefficient-width constructor for an original coprime Cauchy
pair: compute the reduced-chain event and lift its signs back to the supplied
coordinates. -/
def cauchyEventSignsOfRefinedWidth
    (R S : RatPolynomial) (hR : R.isZero = false) (hS : S.isZero = false)
    (coprime : FTA.DenseSquarefree.CoprimeCertificate R S)
    (root interval : FTA.SturmTransducer.RationalInterval)
    (hrefines : interval.Refines root) (proper : interval.Proper)
    (hwidth : interval.width <
      FTA.SturmTransducer.cauchyChainAmbientWidthResolution
        R S hR hS root) :
    CauchyEventSigns R S interval :=
  (reducedCauchyEventSignsOfRefinedWidth R S hR hS root interval
    hrefines proper hwidth).ofCoprime coprime

/-- Symmetric common factor of the two product coordinates formed from two
coprime complex-coordinate pairs. -/
def productCoordinateCommonFactor (A B C D : RatPolynomial) : RatPolynomial :=
  FTA.DenseGCD.symmetricGCD
    (productNumerator A B C D) (productDenominator A B C D)

/-- Uniform upper bound for the squared norm of the two product-coordinate
gcd cofactors. -/
def productCofactorNormMajorant
    (A B C D : RatPolynomial)
    (root : FTA.SturmTransducer.RationalInterval) : ℚ :=
  let E := productNumerator A B C D
  let H := productDenominator A B C D
  let bound := intervalMagnitude root.lower root.upper
  max 1
    (denseEvalAbsBound (reducedNumerator E H) bound ^ 2 +
      denseEvalAbsBound (reducedDenominator E H) bound ^ 2)

theorem productCofactorNormMajorant_pos
    (A B C D : RatPolynomial)
    (root : FTA.SturmTransducer.RationalInterval) :
    0 < productCofactorNormMajorant A B C D root :=
  zero_lt_one.trans_le (le_max_left _ _)

/-- Product of the two Bézout exclusion margins for the factor norms. -/
def productCoordinateNormLower
    {A B C D : RatPolynomial}
    (left : FTA.DenseSquarefree.CoprimeCertificate A B)
    (right : FTA.DenseSquarefree.CoprimeCertificate C D)
    (root : FTA.SturmTransducer.RationalInterval) : ℚ :=
  let bound := intervalMagnitude root.lower root.upper
  coprimeExclusionMargin left bound ^ 2 *
    coprimeExclusionMargin right bound ^ 2

theorem productCoordinateNormLower_pos
    {A B C D : RatPolynomial}
    (left : FTA.DenseSquarefree.CoprimeCertificate A B)
    (right : FTA.DenseSquarefree.CoprimeCertificate C D)
    (root : FTA.SturmTransducer.RationalInterval) :
    0 < productCoordinateNormLower left right root := by
  apply mul_pos <;>
    exact sq_pos_of_pos (coprimeExclusionMargin_pos _
      (intervalMagnitude_pos root.lower root.upper).le)

/-- Positive rational radius forcing the product-coordinate common gcd to
have a coefficient-certified fixed sign.  Squaring avoids any real square
root: the exact complex norm identity supplies the lower bound. -/
def ambientProductCommonFactorRadius
    {A B C D : RatPolynomial}
    (left : FTA.DenseSquarefree.CoprimeCertificate A B)
    (right : FTA.DenseSquarefree.CoprimeCertificate C D)
    (root : FTA.SturmTransducer.RationalInterval) : ℚ :=
  let bound := intervalMagnitude root.lower root.upper
  let g := productCoordinateCommonFactor A B C D
  let slopeSquare := max 1 (denseEvalLipschitzBound g bound ^ 2)
  min 1 (productCoordinateNormLower left right root /
    (productCofactorNormMajorant A B C D root * slopeSquare))

theorem ambientProductCommonFactorRadius_pos
    {A B C D : RatPolynomial}
    (left : FTA.DenseSquarefree.CoprimeCertificate A B)
    (right : FTA.DenseSquarefree.CoprimeCertificate C D)
    (root : FTA.SturmTransducer.RationalInterval) :
    0 < ambientProductCommonFactorRadius left right root := by
  apply lt_min (by norm_num)
  apply div_pos (productCoordinateNormLower_pos left right root)
  apply mul_pos (productCofactorNormMajorant_pos A B C D root)
  exact zero_lt_one.trans_le (le_max_left _ _)

/-- The rational norm lower bound and cofactor upper bound force the common
product-coordinate gcd to pass the actual midpoint sign test on every nested
cell below the computed radius. -/
theorem productCoordinateCommonFactor_midpointResolved_of_ambient
    {A B C D : RatPolynomial}
    (left : FTA.DenseSquarefree.CoprimeCertificate A B)
    (right : FTA.DenseSquarefree.CoprimeCertificate C D)
    (root interval : FTA.SturmTransducer.RationalInterval)
    (hrefines : interval.Refines root) (proper : interval.Proper)
    (hradius : intervalRadius interval.lower interval.upper
        (midpoint interval.lower interval.upper) <
      ambientProductCommonFactorRadius left right root) :
    FTA.SturmTransducer.MidpointResolved interval
      (productCoordinateCommonFactor A B C D) := by
  let E := productNumerator A B C D
  let H := productDenominator A B C D
  let g := productCoordinateCommonFactor A B C D
  let e := reducedNumerator E H
  let h := reducedDenominator E H
  let rootBound := intervalMagnitude root.lower root.upper
  let subBound := intervalMagnitude interval.lower interval.upper
  let sample := midpoint interval.lower interval.upper
  let radius := intervalRadius interval.lower interval.upper sample
  let leftMargin := coprimeExclusionMargin left rootBound
  let rightMargin := coprimeExclusionMargin right rootBound
  let lower := productCoordinateNormLower left right root
  let majorant := productCofactorNormMajorant A B C D root
  let rootSlope := denseEvalLipschitzBound g rootBound
  let subSlope := denseEvalLipschitzBound g subBound
  let slopeSquare := max 1 (rootSlope ^ 2)
  have hrootBound : 0 ≤ rootBound :=
    (intervalMagnitude_pos root.lower root.upper).le
  have hsubBound : 0 ≤ subBound :=
    (intervalMagnitude_pos interval.lower interval.upper).le
  have hmagnitude : subBound ≤ rootBound :=
    interval.intervalMagnitude_le_of_refines hrefines proper
  have hsampleRoot : |sample| ≤ rootBound := by
    apply abs_le_intervalMagnitude
    · exact hrefines.1.trans (lower_lt_midpoint proper).le
    · exact (midpoint_lt_upper proper).le.trans hrefines.2
  have hleftMarginPos : 0 < leftMargin :=
    coprimeExclusionMargin_pos left hrootBound
  have hrightMarginPos : 0 < rightMargin :=
    coprimeExclusionMargin_pos right hrootBound
  have hleftMax : leftMargin ≤
      max |A.eval sample| |B.eval sample| :=
    coprimeExclusionMargin_le_max_abs_eval left hrootBound hsampleRoot
  have hrightMax : rightMargin ≤
      max |C.eval sample| |D.eval sample| :=
    coprimeExclusionMargin_le_max_abs_eval right hrootBound hsampleRoot
  have hleftNorm : leftMargin ^ 2 ≤
      A.eval sample ^ 2 + B.eval sample ^ 2 := by
    rcases le_max_iff.mp hleftMax with hA | hB
    · have hA2 := pow_le_pow_left₀ hleftMarginPos.le hA 2
      rw [sq_abs] at hA2
      exact hA2.trans (le_add_of_nonneg_right (sq_nonneg _))
    · have hB2 := pow_le_pow_left₀ hleftMarginPos.le hB 2
      rw [sq_abs] at hB2
      exact hB2.trans (le_add_of_nonneg_left (sq_nonneg _))
  have hrightNorm : rightMargin ^ 2 ≤
      C.eval sample ^ 2 + D.eval sample ^ 2 := by
    rcases le_max_iff.mp hrightMax with hC | hD
    · have hC2 := pow_le_pow_left₀ hrightMarginPos.le hC 2
      rw [sq_abs] at hC2
      exact hC2.trans (le_add_of_nonneg_right (sq_nonneg _))
    · have hD2 := pow_le_pow_left₀ hrightMarginPos.le hD 2
      rw [sq_abs] at hD2
      exact hD2.trans (le_add_of_nonneg_left (sq_nonneg _))
  have hnormProduct : lower ≤
      (A.eval sample ^ 2 + B.eval sample ^ 2) *
        (C.eval sample ^ 2 + D.eval sample ^ 2) := by
    change leftMargin ^ 2 * rightMargin ^ 2 ≤ _
    exact mul_le_mul hleftNorm hrightNorm
      (sq_nonneg _) (add_nonneg (sq_nonneg _) (sq_nonneg _))
  have hcomplexNorm : E.eval sample ^ 2 + H.eval sample ^ 2 =
      (A.eval sample ^ 2 + B.eval sample ^ 2) *
        (C.eval sample ^ 2 + D.eval sample ^ 2) := by
    simp only [E, H, eval_productNumerator, eval_productDenominator]
    ring
  have hlowerProduct : lower ≤ E.eval sample ^ 2 + H.eval sample ^ 2 := by
    rw [hcomplexNorm]
    exact hnormProduct
  have heBound : |e.eval sample| ≤ denseEvalAbsBound e rootBound :=
    abs_dense_eval_le_denseEvalAbsBound e hrootBound hsampleRoot
  have hhBound : |h.eval sample| ≤ denseEvalAbsBound h rootBound :=
    abs_dense_eval_le_denseEvalAbsBound h hrootBound hsampleRoot
  have heSquare : e.eval sample ^ 2 ≤
      denseEvalAbsBound e rootBound ^ 2 := by
    have := pow_le_pow_left₀ (abs_nonneg (e.eval sample)) heBound 2
    simpa only [sq_abs] using this
  have hhSquare : h.eval sample ^ 2 ≤
      denseEvalAbsBound h rootBound ^ 2 := by
    have := pow_le_pow_left₀ (abs_nonneg (h.eval sample)) hhBound 2
    simpa only [sq_abs] using this
  have hcofactorNorm : e.eval sample ^ 2 + h.eval sample ^ 2 ≤ majorant := by
    apply (add_le_add heSquare hhSquare).trans
    exact le_max_right _ _
  have hfactorNorm : E.eval sample ^ 2 + H.eval sample ^ 2 =
      g.eval sample ^ 2 * (e.eval sample ^ 2 + h.eval sample ^ 2) := by
    have hE := FTA.DenseGCD.symmetricLeftFactor_eval_identity E H sample
    have hH := FTA.DenseGCD.symmetricRightFactor_eval_identity E H sample
    change E.eval sample = g.eval sample * e.eval sample at hE
    change H.eval sample = g.eval sample * h.eval sample at hH
    rw [hE, hH]
    ring
  have hmajorantPos : 0 < majorant :=
    productCofactorNormMajorant_pos A B C D root
  have hlowerScaled : lower ≤ g.eval sample ^ 2 * majorant := by
    calc
      lower ≤ E.eval sample ^ 2 + H.eval sample ^ 2 := hlowerProduct
      _ = g.eval sample ^ 2 *
          (e.eval sample ^ 2 + h.eval sample ^ 2) := hfactorNorm
      _ ≤ g.eval sample ^ 2 * majorant :=
        mul_le_mul_of_nonneg_left hcofactorNorm (sq_nonneg _)
  have hlowerDiv : lower / majorant ≤ g.eval sample ^ 2 := by
    apply (div_le_iff₀ hmajorantPos).2
    simpa only [mul_comm] using hlowerScaled
  have hslopeMono : subSlope ≤ rootSlope :=
    (denseHornerBounds_mono g hsubBound hmagnitude).2
  have hsubSlope : 0 ≤ subSlope :=
    (denseHornerBounds_nonneg g hsubBound).2
  have hrootSlope : 0 ≤ rootSlope :=
    (denseHornerBounds_nonneg g hrootBound).2
  have hslopeSquarePos : 0 < slopeSquare :=
    zero_lt_one.trans_le (le_max_left _ _)
  have hslopeSquared : subSlope ^ 2 ≤ slopeSquare := by
    have hsquare := pow_le_pow_left₀ hsubSlope hslopeMono 2
    exact hsquare.trans (le_max_right _ _)
  have hradiusNonneg : 0 ≤ radius := by
    dsimp only [radius, intervalRadius]
    positivity
  have hradiusOne : radius < 1 := by
    exact hradius.trans_le (by
      dsimp only [ambientProductCommonFactorRadius]
      exact min_le_left _ _)
  have hradiusFraction : radius <
      lower / (majorant * slopeSquare) := by
    exact hradius.trans_le (by
      dsimp only [ambientProductCommonFactorRadius, lower, majorant,
        slopeSquare, rootSlope, g, rootBound]
      exact min_le_right _ _)
  have hradiusSquare : radius ^ 2 ≤ radius := by
    rw [pow_two]
    calc
      radius * radius ≤ radius * 1 :=
        mul_le_mul_of_nonneg_left hradiusOne.le hradiusNonneg
      _ = radius := mul_one _
  have hscaledSquare : (subSlope * radius) ^ 2 ≤ slopeSquare * radius := by
    rw [mul_pow]
    calc
      subSlope ^ 2 * radius ^ 2 ≤ slopeSquare * radius ^ 2 :=
        mul_le_mul_of_nonneg_right hslopeSquared (sq_nonneg _)
      _ ≤ slopeSquare * radius :=
        mul_le_mul_of_nonneg_left hradiusSquare hslopeSquarePos.le
  have hscaledFraction : slopeSquare * radius < lower / majorant := by
    calc
      slopeSquare * radius <
          slopeSquare * (lower / (majorant * slopeSquare)) :=
        mul_lt_mul_of_pos_left hradiusFraction hslopeSquarePos
      _ = lower / majorant := by
        field_simp [hmajorantPos.ne', hslopeSquarePos.ne']
  have hscaledEvalSquare :
      (subSlope * radius) ^ 2 < g.eval sample ^ 2 :=
    (hscaledSquare.trans_lt hscaledFraction).trans_le hlowerDiv
  change subSlope * radius < |g.eval sample|
  by_contra hnot
  have habsLe : |g.eval sample| ≤ subSlope * radius := le_of_not_gt hnot
  have hsquareLe := pow_le_pow_left₀ (abs_nonneg (g.eval sample)) habsLe 2
  rw [sq_abs] at hsquareLe
  exact (not_lt_of_ge hsquareLe hscaledEvalSquare)

/-- Width form of the product-coordinate common-factor radius. -/
def productCoordinateCommonFactorWidthResolution
    {A B C D : RatPolynomial}
    (left : FTA.DenseSquarefree.CoprimeCertificate A B)
    (right : FTA.DenseSquarefree.CoprimeCertificate C D)
    (root : FTA.SturmTransducer.RationalInterval) : ℚ :=
  2 * ambientProductCommonFactorRadius left right root

theorem productCoordinateCommonFactorWidthResolution_pos
    {A B C D : RatPolynomial}
    (left : FTA.DenseSquarefree.CoprimeCertificate A B)
    (right : FTA.DenseSquarefree.CoprimeCertificate C D)
    (root : FTA.SturmTransducer.RationalInterval) :
    0 < productCoordinateCommonFactorWidthResolution left right root :=
  mul_pos (by norm_num)
    (ambientProductCommonFactorRadius_pos left right root)

/-- Every proper nested cell below the computed width coefficient-resolves
the common factor of the two product coordinates. -/
theorem productCoordinateCommonFactor_midpointResolved_of_refined_width
    {A B C D : RatPolynomial}
    (left : FTA.DenseSquarefree.CoprimeCertificate A B)
    (right : FTA.DenseSquarefree.CoprimeCertificate C D)
    (root interval : FTA.SturmTransducer.RationalInterval)
    (hrefines : interval.Refines root) (proper : interval.Proper)
    (hwidth : interval.width <
      productCoordinateCommonFactorWidthResolution left right root) :
    FTA.SturmTransducer.MidpointResolved interval
      (productCoordinateCommonFactor A B C D) := by
  apply productCoordinateCommonFactor_midpointResolved_of_ambient
    left right root interval hrefines proper
  rw [interval.midpointRadius_eq_half_width proper]
  dsimp only [productCoordinateCommonFactorWidthResolution] at hwidth
  linarith

/-- One positive coefficient-computed width that both classifies the reduced
product Cauchy chain and fixes the sign of the possibly nonconstant common
factor relating it to the original product coordinates. -/
def productCauchyEventWidthResolution
    (A B C D : RatPolynomial)
    (hE : (productNumerator A B C D).isZero = false)
    (hH : (productDenominator A B C D).isZero = false)
    (left : FTA.DenseSquarefree.CoprimeCertificate A B)
    (right : FTA.DenseSquarefree.CoprimeCertificate C D)
    (root : FTA.SturmTransducer.RationalInterval) : ℚ :=
  min
    (FTA.SturmTransducer.cauchyChainAmbientWidthResolution
      (productNumerator A B C D) (productDenominator A B C D)
      hE hH root)
    (productCoordinateCommonFactorWidthResolution left right root)

theorem productCauchyEventWidthResolution_pos
    (A B C D : RatPolynomial)
    (hE : (productNumerator A B C D).isZero = false)
    (hH : (productDenominator A B C D).isZero = false)
    (left : FTA.DenseSquarefree.CoprimeCertificate A B)
    (right : FTA.DenseSquarefree.CoprimeCertificate C D)
    (root : FTA.SturmTransducer.RationalInterval) :
    0 < productCauchyEventWidthResolution A B C D
      hE hH left right root := by
  apply lt_min
  · exact FTA.SturmTransducer.cauchyChainAmbientWidthResolution_pos
      (productNumerator A B C D) (productDenominator A B C D)
      hE hH root
  · exact productCoordinateCommonFactorWidthResolution_pos left right root

/-- End-to-end product-coordinate event record.  This is the point where the
common factor created by complex multiplication is handled constructively:
the chain is computed after gcd reduction, then lifted through the
coefficient-resolved polynomial gcd. -/
def productCauchyEventSignsOfRefinedWidth
    (A B C D : RatPolynomial)
    (hE : (productNumerator A B C D).isZero = false)
    (hH : (productDenominator A B C D).isZero = false)
    (left : FTA.DenseSquarefree.CoprimeCertificate A B)
    (right : FTA.DenseSquarefree.CoprimeCertificate C D)
    (root interval : FTA.SturmTransducer.RationalInterval)
    (hrefines : interval.Refines root) (proper : interval.Proper)
    (hwidth : interval.width < productCauchyEventWidthResolution
      A B C D hE hH left right root) :
    CauchyEventSigns (productNumerator A B C D)
      (productDenominator A B C D) interval := by
  have hchain : interval.width <
      FTA.SturmTransducer.cauchyChainAmbientWidthResolution
        (productNumerator A B C D) (productDenominator A B C D)
        hE hH root :=
    hwidth.trans_le (by
      dsimp only [productCauchyEventWidthResolution]
      exact min_le_left _ _)
  have hcommon : interval.width <
      productCoordinateCommonFactorWidthResolution left right root :=
    hwidth.trans_le (by
      dsimp only [productCauchyEventWidthResolution]
      exact min_le_right _ _)
  let data := reducedCauchyEventSignsOfRefinedWidth
    (productNumerator A B C D) (productDenominator A B C D)
    hE hH root interval hrefines proper hchain
  exact data.ofResolvedCommonFactor proper
    (productCoordinateCommonFactor_midpointResolved_of_refined_width
      left right root interval hrefines proper hcommon)

/-- Assemble the three independently computed Cauchy-pair center records into
the six signs expected by the product-event table. -/
def productEventSignsOfCauchyEvents
    {A B C D : RatPolynomial}
    {interval : FTA.SturmTransducer.RationalInterval}
    (left : CauchyEventSigns A B interval)
    (right : CauchyEventSigns C D interval)
    (product : CauchyEventSigns (productNumerator A B C D)
      (productDenominator A B C D) interval) : EventSigns where
  factorLeftReal := left.numerator
  factorLeftImag := left.denominator
  factorRightReal := right.numerator
  factorRightImag := right.denominator
  productReal := product.numerator
  productImag := product.denominator

/-- Once the computed formal center respects complex multiplication, the
three exact Cauchy-event records supply every field of the exhaustive
two-sided product-event checker. -/
theorem productEventSignsOfCauchyEvents_certifies
    {A B C D : RatPolynomial}
    {interval : FTA.SturmTransducer.RationalInterval}
    (left : CauchyEventSigns A B interval)
    (right : CauchyEventSigns C D interval)
    (product : CauchyEventSigns (productNumerator A B C D)
      (productDenominator A B C D) interval)
    (hcenter : FiniteSign.ComplexProductCompatible
      left.numerator left.denominator right.numerator right.denominator
      product.numerator product.denominator)
    (hBLower : B.eval interval.lower ≠ 0)
    (hDLower : D.eval interval.lower ≠ 0)
    (hHLower : (productDenominator A B C D).eval interval.lower ≠ 0)
    (hBUpper : B.eval interval.upper ≠ 0)
    (hDUpper : D.eval interval.upper ≠ 0)
    (hHUpper : (productDenominator A B C D).eval interval.upper ≠ 0) :
    (productEventSignsOfCauchyEvents left right product).Certifies
      A B C D interval.lower interval.upper := by
  have hBLowerSign : FiniteSign.ofRat (B.eval interval.lower) ≠ .zero := by
    simpa [FiniteSign.ofRat_eq_zero_iff] using hBLower
  have hDLowerSign : FiniteSign.ofRat (D.eval interval.lower) ≠ .zero := by
    simpa [FiniteSign.ofRat_eq_zero_iff] using hDLower
  have hHLowerSign :
      FiniteSign.ofRat
        ((productDenominator A B C D).eval interval.lower) ≠ .zero := by
    simpa [FiniteSign.ofRat_eq_zero_iff] using hHLower
  have hBUpperSign : FiniteSign.ofRat (B.eval interval.upper) ≠ .zero := by
    simpa [FiniteSign.ofRat_eq_zero_iff] using hBUpper
  have hDUpperSign : FiniteSign.ofRat (D.eval interval.upper) ≠ .zero := by
    simpa [FiniteSign.ofRat_eq_zero_iff] using hDUpper
  have hHUpperSign :
      FiniteSign.ofRat
        ((productDenominator A B C D).eval interval.upper) ≠ .zero := by
    simpa [FiniteSign.ofRat_eq_zero_iff] using hHUpper
  unfold EventSigns.Certifies
  refine ⟨?_, ?_, ?_, ?_, ?_⟩
  · refine ⟨left.nonzero, right.nonzero, hBLowerSign, hDLowerSign,
      hHLowerSign, left.numeratorLowerStable,
      left.denominatorLowerStable, right.numeratorLowerStable,
      right.denominatorLowerStable, product.numeratorLowerStable,
      product.denominatorLowerStable, hcenter, ?_⟩
    simpa only [eval_productNumerator, eval_productDenominator] using
      finiteSign_complexProductCompatible
        (A.eval interval.lower) (B.eval interval.lower)
        (C.eval interval.lower) (D.eval interval.lower)
  · refine ⟨left.nonzero, right.nonzero, hBUpperSign, hDUpperSign,
      hHUpperSign, left.numeratorUpperStable,
      left.denominatorUpperStable, right.numeratorUpperStable,
      right.denominatorUpperStable, product.numeratorUpperStable,
      product.denominatorUpperStable, hcenter, ?_⟩
    simpa only [eval_productNumerator, eval_productDenominator] using
      finiteSign_complexProductCompatible
        (A.eval interval.upper) (B.eval interval.upper)
        (C.eval interval.upper) (D.eval interval.upper)
  · simpa only [productEventSignsOfCauchyEvents] using left.index
  · simpa only [productEventSignsOfCauchyEvents] using right.index
  · simpa only [productEventSignsOfCauchyEvents] using product.index

/-- Therefore a compatible triple of computed Cauchy-event records makes the
genuine exhaustive product leaf classifier return a partition. -/
theorem localProductLeaf?_isSome_of_cauchyEventSigns
    {A B C D : RatPolynomial}
    {interval : FTA.SturmTransducer.RationalInterval}
    (left : CauchyEventSigns A B interval)
    (right : CauchyEventSigns C D interval)
    (product : CauchyEventSigns (productNumerator A B C D)
      (productDenominator A B C D) interval)
    (hcenter : FiniteSign.ComplexProductCompatible
      left.numerator left.denominator right.numerator right.denominator
      product.numerator product.denominator)
    (hBLower : B.eval interval.lower ≠ 0)
    (hDLower : D.eval interval.lower ≠ 0)
    (hHLower : (productDenominator A B C D).eval interval.lower ≠ 0)
    (hBUpper : B.eval interval.upper ≠ 0)
    (hDUpper : D.eval interval.upper ≠ 0)
    (hHUpper : (productDenominator A B C D).eval interval.upper ≠ 0) :
    (localProductLeaf? A B C D interval.lower interval.upper).isSome := by
  let signs := productEventSignsOfCauchyEvents left right product
  have hcertifies : signs.Certifies A B C D
      interval.lower interval.upper :=
    productEventSignsOfCauchyEvents_certifies left right product hcenter
      hBLower hDLower hHLower hBUpper hDUpper hHUpper
  have hdata := localEventData?_isSome_of_certifies signs hcertifies
  rcases Option.isSome_iff_exists.mp hdata with ⟨data, hdata⟩
  rw [localProductLeaf?_def, hdata]
  rfl

/-- A coordinated triple is the complete center-side input expected by the
genuine exhaustive leaf; only the six rational endpoint nonvanishing guards
remain explicit. -/
theorem CompatibleCauchyEventTriple.localProductLeaf?_isSome
    {A B C D : RatPolynomial}
    {interval : FTA.SturmTransducer.RationalInterval}
    (triple : CompatibleCauchyEventTriple A B C D interval)
    (hBLower : B.eval interval.lower ≠ 0)
    (hDLower : D.eval interval.lower ≠ 0)
    (hHLower : (productDenominator A B C D).eval interval.lower ≠ 0)
    (hBUpper : B.eval interval.upper ≠ 0)
    (hDUpper : D.eval interval.upper ≠ 0)
    (hHUpper : (productDenominator A B C D).eval interval.upper ≠ 0) :
    (localProductLeaf? A B C D interval.lower interval.upper).isSome :=
  localProductLeaf?_isSome_of_cauchyEventSigns
    triple.left triple.right triple.product triple.compatible
    hBLower hDLower hHLower hBUpper hDUpper hHUpper

/-- One positive width resolving the three exact Cauchy chains together with
all six one-sided endpoint signs.  Unlike the interior-event width, this
boundary width needs no turn estimate because the formal centers are fixed
to the exact endpoint values. -/
def coordinatedProductEndpointWidthResolution
    (A B C D : RatPolynomial)
    (hA : A.isZero = false) (hB : B.isZero = false)
    (hC : C.isZero = false) (hD : D.isZero = false)
    (hE : (productNumerator A B C D).isZero = false)
    (hH : (productDenominator A B C D).isZero = false)
    (left : FTA.DenseSquarefree.CoprimeCertificate A B)
    (right : FTA.DenseSquarefree.CoprimeCertificate C D)
    (root : FTA.SturmTransducer.RationalInterval) (x : ℚ) : ℚ :=
  min
    (FTA.SturmTransducer.cauchyChainAmbientWidthResolution
      A B hA hB root)
    (min
      (FTA.SturmTransducer.cauchyChainAmbientWidthResolution
        C D hC hD root)
      (min
        (productCauchyEventWidthResolution
          A B C D hE hH left right root)
        (productEndpointStabilityWidth A B C D root x)))

theorem coordinatedProductEndpointWidthResolution_pos
    (A B C D : RatPolynomial)
    (hA : A.isZero = false) (hB : B.isZero = false)
    (hC : C.isZero = false) (hD : D.isZero = false)
    (hE : (productNumerator A B C D).isZero = false)
    (hH : (productDenominator A B C D).isZero = false)
    (left : FTA.DenseSquarefree.CoprimeCertificate A B)
    (right : FTA.DenseSquarefree.CoprimeCertificate C D)
    (root : FTA.SturmTransducer.RationalInterval) (x : ℚ) :
    0 < coordinatedProductEndpointWidthResolution
      A B C D hA hB hC hD hE hH left right root x := by
  dsimp only [coordinatedProductEndpointWidthResolution]
  apply lt_min
  · exact FTA.SturmTransducer.cauchyChainAmbientWidthResolution_pos
      A B hA hB root
  · apply lt_min
    · exact FTA.SturmTransducer.cauchyChainAmbientWidthResolution_pos
        C D hC hD root
    · apply lt_min
      · exact productCauchyEventWidthResolution_pos
          A B C D hE hH left right root
      · exact productEndpointStabilityWidth_pos A B C D root x

/-- One coefficient-computed width combining the two factor Cauchy chains,
the product Cauchy chain and its common-factor lift, and coordinated center
turns. -/
def coordinatedProductEventWidthResolution
    (A B C D : RatPolynomial)
    (hA : A.isZero = false) (hB : B.isZero = false)
    (hC : C.isZero = false) (hD : D.isZero = false)
    (hE : (productNumerator A B C D).isZero = false)
    (hH : (productDenominator A B C D).isZero = false)
    (left : FTA.DenseSquarefree.CoprimeCertificate A B)
    (right : FTA.DenseSquarefree.CoprimeCertificate C D)
    (root : FTA.SturmTransducer.RationalInterval) : ℚ :=
  min (FTA.SturmTransducer.cauchyChainAmbientWidthResolution
      A B hA hB root)
    (min (FTA.SturmTransducer.cauchyChainAmbientWidthResolution
        C D hC hD root)
      (min (productCauchyEventWidthResolution
          A B C D hE hH left right root)
        (ProductCenterSigns.turnWidthResolution left right root)))

theorem coordinatedProductEventWidthResolution_pos
    (A B C D : RatPolynomial)
    (hA : A.isZero = false) (hB : B.isZero = false)
    (hC : C.isZero = false) (hD : D.isZero = false)
    (hE : (productNumerator A B C D).isZero = false)
    (hH : (productDenominator A B C D).isZero = false)
    (left : FTA.DenseSquarefree.CoprimeCertificate A B)
    (right : FTA.DenseSquarefree.CoprimeCertificate C D)
    (root : FTA.SturmTransducer.RationalInterval) :
    0 < coordinatedProductEventWidthResolution
      A B C D hA hB hC hD hE hH left right root := by
  apply lt_min
  · exact FTA.SturmTransducer.cauchyChainAmbientWidthResolution_pos
      A B hA hB root
  · apply lt_min
    · exact FTA.SturmTransducer.cauchyChainAmbientWidthResolution_pos
        C D hC hD root
    · apply lt_min
      · exact productCauchyEventWidthResolution_pos
          A B C D hE hH left right root
      · exact ProductCenterSigns.turnWidthResolution_pos left right root

/-- End-to-end success of the genuine exhaustive product leaf on a clear
event cell below the combined coefficient width. -/
def localProductLeaf?_succeeds_of_coordinated_refined_width
    (A B C D : RatPolynomial)
    (hA : A.isZero = false) (hB : B.isZero = false)
    (hC : C.isZero = false) (hD : D.isZero = false)
    (hE : (productNumerator A B C D).isZero = false)
    (hH : (productDenominator A B C D).isZero = false)
    (left : FTA.DenseSquarefree.CoprimeCertificate A B)
    (right : FTA.DenseSquarefree.CoprimeCertificate C D)
    (root interval : FTA.SturmTransducer.RationalInterval)
    (hrefines : interval.Refines root) (proper : interval.Proper)
    (hwidth : interval.width < coordinatedProductEventWidthResolution
      A B C D hA hB hC hD hE hH left right root)
    (hAₗ : A.eval interval.lower ≠ 0)
    (hBₗ : B.eval interval.lower ≠ 0)
    (hCₗ : C.eval interval.lower ≠ 0)
    (hDₗ : D.eval interval.lower ≠ 0)
    (hEₗ : (productNumerator A B C D).eval interval.lower ≠ 0)
    (hHₗ : (productDenominator A B C D).eval interval.lower ≠ 0)
    (hAᵣ : A.eval interval.upper ≠ 0)
    (hBᵣ : B.eval interval.upper ≠ 0)
    (hCᵣ : C.eval interval.upper ≠ 0)
    (hDᵣ : D.eval interval.upper ≠ 0)
    (hEᵣ : (productNumerator A B C D).eval interval.upper ≠ 0)
    (hHᵣ : (productDenominator A B C D).eval interval.upper ≠ 0) :
    { partition : AuxiliaryProductPartition A B C D
        interval.lower interval.upper //
      localProductLeaf? A B C D interval.lower interval.upper =
        some partition } := by
  have hleftWidth : interval.width <
      FTA.SturmTransducer.cauchyChainAmbientWidthResolution
        A B hA hB root :=
    hwidth.trans_le (by
      dsimp only [coordinatedProductEventWidthResolution]
      exact min_le_left _ _)
  have hrightWidth : interval.width <
      FTA.SturmTransducer.cauchyChainAmbientWidthResolution
        C D hC hD root :=
    hwidth.trans_le (by
      dsimp only [coordinatedProductEventWidthResolution]
      exact (min_le_right _ _).trans (min_le_left _ _))
  have hproductWidth : interval.width <
      productCauchyEventWidthResolution
        A B C D hE hH left right root :=
    hwidth.trans_le (by
      dsimp only [coordinatedProductEventWidthResolution]
      exact (min_le_right _ _).trans
        ((min_le_right _ _).trans (min_le_left _ _)))
  have hturnWidth : interval.width <
      ProductCenterSigns.turnWidthResolution left right root :=
    hwidth.trans_le (by
      dsimp only [coordinatedProductEventWidthResolution]
      exact (min_le_right _ _).trans
        ((min_le_right _ _).trans (min_le_right _ _)))
  let leftBase := cauchyEventSignsOfRefinedWidth
    A B hA hB left root interval hrefines proper hleftWidth
  let rightBase := cauchyEventSignsOfRefinedWidth
    C D hC hD right root interval hrefines proper hrightWidth
  let productBase := productCauchyEventSignsOfRefinedWidth
    A B C D hE hH left right root interval hrefines proper hproductWidth
  have htripleSome :=
    CompatibleCauchyEventTriple.search?_isSome_of_refined_width
      leftBase rightBase productBase left right root hrefines proper hturnWidth
      hAₗ hBₗ hCₗ hDₗ hEₗ hHₗ hAᵣ hBᵣ hCᵣ hDᵣ hEᵣ hHᵣ
  cases htriple : CompatibleCauchyEventTriple.search?
      leftBase rightBase productBase with
  | none => simp [htriple] at htripleSome
  | some triple =>
      have hleafSome := triple.localProductLeaf?_isSome
        hBₗ hDₗ hHₗ hBᵣ hDᵣ hHᵣ
      cases hleaf : localProductLeaf? A B C D
          interval.lower interval.upper with
      | none => simp [hleaf] at hleafSome
      | some partition => exact ⟨partition, rfl⟩

/-- End-to-end success of the genuine one-sided endpoint leaf for a refined
cell whose left endpoint is the fixed ambient boundary and whose opposite
denominators are clear.  The three exact event records are re-centered at
the rational boundary, so their indices become the endpoint pole terms
checked by `localEndpointData?`. -/
def localProductLeaf?_succeeds_of_left_endpoint_refined_width
    (A B C D : RatPolynomial)
    (hA : A.isZero = false) (hB : B.isZero = false)
    (hC : C.isZero = false) (hD : D.isZero = false)
    (hE : (productNumerator A B C D).isZero = false)
    (hH : (productDenominator A B C D).isZero = false)
    (left : FTA.DenseSquarefree.CoprimeCertificate A B)
    (right : FTA.DenseSquarefree.CoprimeCertificate C D)
    (root interval : FTA.SturmTransducer.RationalInterval)
    (hrefines : interval.Refines root) (proper : interval.Proper)
    (hlower : interval.lower = root.lower)
    (hwidth : interval.width <
      coordinatedProductEndpointWidthResolution
        A B C D hA hB hC hD hE hH left right root root.lower)
    (hBUpper : B.eval interval.upper ≠ 0)
    (hDUpper : D.eval interval.upper ≠ 0)
    (hHUpper : (productDenominator A B C D).eval interval.upper ≠ 0) :
    { partition : AuxiliaryProductPartition A B C D
        interval.lower interval.upper //
      localProductLeaf? A B C D interval.lower interval.upper =
        some partition } := by
  have hleftWidth : interval.width <
      FTA.SturmTransducer.cauchyChainAmbientWidthResolution
        A B hA hB root :=
    hwidth.trans_le (by
      dsimp only [coordinatedProductEndpointWidthResolution]
      exact min_le_left _ _)
  have hrightWidth : interval.width <
      FTA.SturmTransducer.cauchyChainAmbientWidthResolution
        C D hC hD root :=
    hwidth.trans_le (by
      dsimp only [coordinatedProductEndpointWidthResolution]
      exact (min_le_right _ _).trans (min_le_left _ _))
  have hproductWidth : interval.width <
      productCauchyEventWidthResolution
        A B C D hE hH left right root :=
    hwidth.trans_le (by
      dsimp only [coordinatedProductEndpointWidthResolution]
      exact (min_le_right _ _).trans
        ((min_le_right _ _).trans (min_le_left _ _)))
  have hendpointWidth : interval.width <
      productEndpointStabilityWidth A B C D root root.lower :=
    hwidth.trans_le (by
      dsimp only [coordinatedProductEndpointWidthResolution]
      exact (min_le_right _ _).trans
        ((min_le_right _ _).trans (min_le_right _ _)))
  have hrootProper : root.Proper :=
    lt_of_le_of_lt hrefines.1 (proper.trans_le hrefines.2)
  have hdistanceEq : |root.lower - interval.upper| = interval.width := by
    rw [← hlower]
    dsimp only [FTA.SturmTransducer.RationalInterval.width]
    rw [abs_of_nonpos (sub_nonpos.mpr proper.le)]
    ring
  have hstabilities := productEndpointStability_of_distance
    A B C D root
    (x := root.lower) (y := interval.upper)
    le_rfl hrootProper.le (hrefines.1.trans proper.le) hrefines.2
    (by simpa only [hdistanceEq] using hendpointWidth)
  rcases hstabilities with
    ⟨hAstable, hBstable, hCstable, hDstable, hEstable, hHstable⟩
  have hfactorLeft :
      A.eval interval.lower ≠ 0 ∨ B.eval interval.lower ≠ 0 := by
    simpa only [hlower] using coprimePair_eval_ne_zero left root.lower
  have hfactorRight :
      C.eval interval.lower ≠ 0 ∨ D.eval interval.lower ≠ 0 := by
    simpa only [hlower] using coprimePair_eval_ne_zero right root.lower
  have hfactorProduct :
      (productNumerator A B C D).eval interval.lower ≠ 0 ∨
        (productDenominator A B C D).eval interval.lower ≠ 0 := by
    simpa only [eval_productNumerator, eval_productDenominator] using
      (complexProductCoordinates_ne_zero hfactorLeft hfactorRight)
  let leftBase := cauchyEventSignsOfRefinedWidth
    A B hA hB left root interval hrefines proper hleftWidth
  let rightBase := cauchyEventSignsOfRefinedWidth
    C D hC hD right root interval hrefines proper hrightWidth
  let productBase := productCauchyEventSignsOfRefinedWidth
    A B C D hE hH left right root interval hrefines proper hproductWidth
  have hleftIndex := leftBase.index_eq_leftEndpointIndex2
    hfactorLeft
    (by simpa only [hlower] using hAstable)
    (by simpa only [hlower] using hBstable)
  have hrightIndex := rightBase.index_eq_leftEndpointIndex2
    hfactorRight
    (by simpa only [hlower] using hCstable)
    (by simpa only [hlower] using hDstable)
  have hproductIndex := productBase.index_eq_leftEndpointIndex2
    hfactorProduct
    (by simpa only [hlower] using hEstable)
    (by simpa only [hlower] using hHstable)
  have hconditions : LocalEndpointConditions A B C D
      interval.lower interval.upper :=
    ⟨hleftIndex, hrightIndex, hproductIndex,
      hfactorLeft, hfactorRight, hBUpper, hDUpper, hHUpper,
      by simpa only [hlower] using hAstable,
      by simpa only [hlower] using hBstable,
      by simpa only [hlower] using hCstable,
      by simpa only [hlower] using hDstable,
      by simpa only [hlower] using hEstable,
      by simpa only [hlower] using hHstable⟩
  have hendpointSome := localEndpointData?_isSome_of_conditions hconditions
  cases hendpointData : localEndpointData? A B C D
      interval.lower interval.upper with
  | none => simp [hendpointData] at hendpointSome
  | some endpointData =>
      have hleafSome :
          (localProductLeaf? A B C D
            interval.lower interval.upper).isSome := by
        rw [localProductLeaf?_def]
        split
        · rfl
        · simp only [hendpointData, Option.isSome_some]
      cases hleaf : localProductLeaf? A B C D
          interval.lower interval.upper with
      | none => simp [hleaf] at hleafSome
      | some partition => exact ⟨partition, rfl⟩

/-- Symmetric right-boundary success theorem.  The exact event records are
re-centered at the ambient upper endpoint and their Cauchy indices are
reversed before the executable classifier's final endpoint branch is used. -/
def localProductLeaf?_succeeds_of_right_endpoint_refined_width
    (A B C D : RatPolynomial)
    (hA : A.isZero = false) (hB : B.isZero = false)
    (hC : C.isZero = false) (hD : D.isZero = false)
    (hE : (productNumerator A B C D).isZero = false)
    (hH : (productDenominator A B C D).isZero = false)
    (left : FTA.DenseSquarefree.CoprimeCertificate A B)
    (right : FTA.DenseSquarefree.CoprimeCertificate C D)
    (root interval : FTA.SturmTransducer.RationalInterval)
    (hrefines : interval.Refines root) (proper : interval.Proper)
    (hupper : interval.upper = root.upper)
    (hwidth : interval.width <
      coordinatedProductEndpointWidthResolution
        A B C D hA hB hC hD hE hH left right root root.upper)
    (hBLower : B.eval interval.lower ≠ 0)
    (hDLower : D.eval interval.lower ≠ 0)
    (hHLower : (productDenominator A B C D).eval interval.lower ≠ 0) :
    { partition : AuxiliaryProductPartition A B C D
        interval.lower interval.upper //
      localProductLeaf? A B C D interval.lower interval.upper =
        some partition } := by
  have hleftWidth : interval.width <
      FTA.SturmTransducer.cauchyChainAmbientWidthResolution
        A B hA hB root :=
    hwidth.trans_le (by
      dsimp only [coordinatedProductEndpointWidthResolution]
      exact min_le_left _ _)
  have hrightWidth : interval.width <
      FTA.SturmTransducer.cauchyChainAmbientWidthResolution
        C D hC hD root :=
    hwidth.trans_le (by
      dsimp only [coordinatedProductEndpointWidthResolution]
      exact (min_le_right _ _).trans (min_le_left _ _))
  have hproductWidth : interval.width <
      productCauchyEventWidthResolution
        A B C D hE hH left right root :=
    hwidth.trans_le (by
      dsimp only [coordinatedProductEndpointWidthResolution]
      exact (min_le_right _ _).trans
        ((min_le_right _ _).trans (min_le_left _ _)))
  have hendpointWidth : interval.width <
      productEndpointStabilityWidth A B C D root root.upper :=
    hwidth.trans_le (by
      dsimp only [coordinatedProductEndpointWidthResolution]
      exact (min_le_right _ _).trans
        ((min_le_right _ _).trans (min_le_right _ _)))
  have hrootProper : root.Proper :=
    lt_of_le_of_lt hrefines.1 (proper.trans_le hrefines.2)
  have hdistanceEq : |root.upper - interval.lower| = interval.width := by
    rw [← hupper]
    dsimp only [FTA.SturmTransducer.RationalInterval.width]
    rw [abs_of_nonneg (sub_nonneg.mpr proper.le)]
  have hstabilities := productEndpointStability_of_distance
    A B C D root
    (x := root.upper) (y := interval.lower)
    hrootProper.le le_rfl hrefines.1 (proper.le.trans hrefines.2)
    (by simpa only [hdistanceEq] using hendpointWidth)
  rcases hstabilities with
    ⟨hAstable, hBstable, hCstable, hDstable, hEstable, hHstable⟩
  have hfactorLeft :
      A.eval interval.upper ≠ 0 ∨ B.eval interval.upper ≠ 0 := by
    simpa only [hupper] using coprimePair_eval_ne_zero left root.upper
  have hfactorRight :
      C.eval interval.upper ≠ 0 ∨ D.eval interval.upper ≠ 0 := by
    simpa only [hupper] using coprimePair_eval_ne_zero right root.upper
  have hfactorProduct :
      (productNumerator A B C D).eval interval.upper ≠ 0 ∨
        (productDenominator A B C D).eval interval.upper ≠ 0 := by
    simpa only [eval_productNumerator, eval_productDenominator] using
      (complexProductCoordinates_ne_zero hfactorLeft hfactorRight)
  let leftBase := cauchyEventSignsOfRefinedWidth
    A B hA hB left root interval hrefines proper hleftWidth
  let rightBase := cauchyEventSignsOfRefinedWidth
    C D hC hD right root interval hrefines proper hrightWidth
  let productBase := productCauchyEventSignsOfRefinedWidth
    A B C D hE hH left right root interval hrefines proper hproductWidth
  have hleftIndex := leftBase.reverse_index_eq_leftEndpointIndex2
    hfactorLeft
    (by simpa only [hupper] using hAstable)
    (by simpa only [hupper] using hBstable)
  have hrightIndex := rightBase.reverse_index_eq_leftEndpointIndex2
    hfactorRight
    (by simpa only [hupper] using hCstable)
    (by simpa only [hupper] using hDstable)
  have hproductIndex := productBase.reverse_index_eq_leftEndpointIndex2
    hfactorProduct
    (by simpa only [hupper] using hEstable)
    (by simpa only [hupper] using hHstable)
  have hconditions : LocalEndpointConditions A B C D
      interval.upper interval.lower :=
    ⟨hleftIndex, hrightIndex, hproductIndex,
      hfactorLeft, hfactorRight, hBLower, hDLower, hHLower,
      by simpa only [hupper] using hAstable,
      by simpa only [hupper] using hBstable,
      by simpa only [hupper] using hCstable,
      by simpa only [hupper] using hDstable,
      by simpa only [hupper] using hEstable,
      by simpa only [hupper] using hHstable⟩
  have hendpointSome := localEndpointData?_isSome_of_conditions hconditions
  cases hendpointData : localEndpointData? A B C D
      interval.upper interval.lower with
  | none => simp [hendpointData] at hendpointSome
  | some endpointData =>
      have hleafSome :
          (localProductLeaf? A B C D
            interval.lower interval.upper).isSome := by
        rw [localProductLeaf?_def]
        split
        · rfl
        · split
          · rfl
          · simp only [hendpointData, Option.isSome_some]
      cases hleaf : localProductLeaf? A B C D
          interval.lower interval.upper with
      | none => simp [hleaf] at hleafSome
      | some partition => exact ⟨partition, rfl⟩

/-- One local width covering the interior coordinated-event case and both
fixed ambient endpoint cases. -/
def completeProductLeafWidthResolution
    (A B C D : RatPolynomial)
    (hA : A.isZero = false) (hB : B.isZero = false)
    (hC : C.isZero = false) (hD : D.isZero = false)
    (hE : (productNumerator A B C D).isZero = false)
    (hH : (productDenominator A B C D).isZero = false)
    (left : FTA.DenseSquarefree.CoprimeCertificate A B)
    (right : FTA.DenseSquarefree.CoprimeCertificate C D)
    (root : FTA.SturmTransducer.RationalInterval) : ℚ :=
  min
    (coordinatedProductEventWidthResolution
      A B C D hA hB hC hD hE hH left right root)
    (min
      (coordinatedProductEndpointWidthResolution
        A B C D hA hB hC hD hE hH left right root root.lower)
      (coordinatedProductEndpointWidthResolution
        A B C D hA hB hC hD hE hH left right root root.upper))

theorem completeProductLeafWidthResolution_pos
    (A B C D : RatPolynomial)
    (hA : A.isZero = false) (hB : B.isZero = false)
    (hC : C.isZero = false) (hD : D.isZero = false)
    (hE : (productNumerator A B C D).isZero = false)
    (hH : (productDenominator A B C D).isZero = false)
    (left : FTA.DenseSquarefree.CoprimeCertificate A B)
    (right : FTA.DenseSquarefree.CoprimeCertificate C D)
    (root : FTA.SturmTransducer.RationalInterval) :
    0 < completeProductLeafWidthResolution
      A B C D hA hB hC hD hE hH left right root := by
  dsimp only [completeProductLeafWidthResolution]
  apply lt_min
  · exact coordinatedProductEventWidthResolution_pos
      A B C D hA hB hC hD hE hH left right root
  · apply lt_min
    · exact coordinatedProductEndpointWidthResolution_pos
        A B C D hA hB hC hD hE hH left right root root.lower
    · exact coordinatedProductEndpointWidthResolution_pos
        A B C D hA hB hC hD hE hH left right root root.upper

/-- The complete coefficient widths instantiate the guard-aware operational
resolution consumed by the actual product partition builder. -/
def guardedProductEventClassifierResolution
    (A B C D : RatPolynomial)
    (hA : A.isZero = false) (hB : B.isZero = false)
    (hC : C.isZero = false) (hD : D.isZero = false)
    (hE : (productNumerator A B C D).isZero = false)
    (hH : (productDenominator A B C D).isZero = false)
    (left : FTA.DenseSquarefree.CoprimeCertificate A B)
    (right : FTA.DenseSquarefree.CoprimeCertificate C D)
    (root : FTA.SturmTransducer.RationalInterval) :
    GuardedProductEventClassifierResolution
      A B C D root.lower root.upper where
  threshold := completeProductLeafWidthResolution
    A B C D hA hB hC hD hE hH left right root
  positive := completeProductLeafWidthResolution_pos
    A B C D hA hB hC hD hE hH left right root
  classify := by
    intro a b hlower hupper hab hwidth hlowerGuard hupperGuard hstrict
    let interval : FTA.SturmTransducer.RationalInterval := ⟨a, b⟩
    have hrefines : interval.Refines root := ⟨hlower, hupper⟩
    have proper : interval.Proper := hab
    have heventWidth : interval.width <
        coordinatedProductEventWidthResolution
          A B C D hA hB hC hD hE hH left right root :=
      hwidth.trans_le (by
        dsimp only [interval, FTA.SturmTransducer.RationalInterval.width,
          completeProductLeafWidthResolution]
        exact min_le_left _ _)
    have hleftEndpointWidth : interval.width <
        coordinatedProductEndpointWidthResolution
          A B C D hA hB hC hD hE hH left right root root.lower :=
      hwidth.trans_le (by
        dsimp only [interval, FTA.SturmTransducer.RationalInterval.width,
          completeProductLeafWidthResolution]
        exact (min_le_right _ _).trans (min_le_left _ _))
    have hrightEndpointWidth : interval.width <
        coordinatedProductEndpointWidthResolution
          A B C D hA hB hC hD hE hH left right root root.upper :=
      hwidth.trans_le (by
        dsimp only [interval, FTA.SturmTransducer.RationalInterval.width,
          completeProductLeafWidthResolution]
        exact (min_le_right _ _).trans (min_le_right _ _))
    have coordinateClear : ∀ x : ℚ,
        (productEventGuard A B C D).eval x ≠ 0 →
        A.eval x ≠ 0 ∧ B.eval x ≠ 0 ∧ C.eval x ≠ 0 ∧ D.eval x ≠ 0 ∧
          (productNumerator A B C D).eval x ≠ 0 ∧
          (productDenominator A B C D).eval x ≠ 0 := by
      intro x hguard
      refine ⟨?_, ?_, ?_, ?_, ?_, ?_⟩
      · exact productEventPolynomial_eval_ne_zero
          (by simp [productEventPolynomials]) hA hguard
      · exact productEventPolynomial_eval_ne_zero
          (by simp [productEventPolynomials]) hB hguard
      · exact productEventPolynomial_eval_ne_zero
          (by simp [productEventPolynomials]) hC hguard
      · exact productEventPolynomial_eval_ne_zero
          (by simp [productEventPolynomials]) hD hguard
      · exact productEventPolynomial_eval_ne_zero
          (by simp [productEventPolynomials]) hE hguard
      · exact productEventPolynomial_eval_ne_zero
          (by simp [productEventPolynomials]) hH hguard
    by_cases hlowerEq : a = root.lower
    · have hupperNe : b ≠ root.upper := by
        intro hupperEq
        exact hstrict.elim (fun h => h hlowerEq) (fun h => h hupperEq)
      have hupperClear := hupperGuard.resolve_left hupperNe
      rcases coordinateClear b hupperClear with
        ⟨-, hBUpper, -, hDUpper, -, hHUpper⟩
      exact localProductLeaf?_succeeds_of_left_endpoint_refined_width
        A B C D hA hB hC hD hE hH left right root interval
        hrefines proper (by simpa only [interval] using hlowerEq)
        hleftEndpointWidth
        (by simpa only [interval] using hBUpper)
        (by simpa only [interval] using hDUpper)
        (by simpa only [interval] using hHUpper)
    · have hlowerClear := hlowerGuard.resolve_left hlowerEq
      by_cases hupperEq : b = root.upper
      · rcases coordinateClear a hlowerClear with
          ⟨-, hBLower, -, hDLower, -, hHLower⟩
        exact localProductLeaf?_succeeds_of_right_endpoint_refined_width
          A B C D hA hB hC hD hE hH left right root interval
          hrefines proper (by simpa only [interval] using hupperEq)
          hrightEndpointWidth
          (by simpa only [interval] using hBLower)
          (by simpa only [interval] using hDLower)
          (by simpa only [interval] using hHLower)
      · have hupperClear := hupperGuard.resolve_left hupperEq
        rcases coordinateClear a hlowerClear with
          ⟨hALower, hBLower, hCLower, hDLower, hELower, hHLower⟩
        rcases coordinateClear b hupperClear with
          ⟨hAUpper, hBUpper, hCUpper, hDUpper, hEUpper, hHUpper⟩
        exact localProductLeaf?_succeeds_of_coordinated_refined_width
          A B C D hA hB hC hD hE hH left right root interval
          hrefines proper heventWidth
          (by simpa only [interval] using hALower)
          (by simpa only [interval] using hBLower)
          (by simpa only [interval] using hCLower)
          (by simpa only [interval] using hDLower)
          (by simpa only [interval] using hELower)
          (by simpa only [interval] using hHLower)
          (by simpa only [interval] using hAUpper)
          (by simpa only [interval] using hBUpper)
          (by simpa only [interval] using hCUpper)
          (by simpa only [interval] using hDUpper)
          (by simpa only [interval] using hEUpper)
          (by simpa only [interval] using hHUpper)

/-- Total finite auxiliary-product partition program for the nondegenerate
coprime-coordinate branch.  Its fuel is the explicit rational ceiling depth
of the complete guard-aware local resolution. -/
def constructiveAuxiliaryProductPartitionProgram
    (A B C D : RatPolynomial)
    (hA : A.isZero = false) (hB : B.isZero = false)
    (hC : C.isZero = false) (hD : D.isZero = false)
    (hE : (productNumerator A B C D).isZero = false)
    (hH : (productDenominator A B C D).isZero = false)
    (left : FTA.DenseSquarefree.CoprimeCertificate A B)
    (right : FTA.DenseSquarefree.CoprimeCertificate C D) :
    AuxiliaryProductPartitionProgram A B C D where
  run := by
    intro a b hab
    let root : FTA.SturmTransducer.RationalInterval := ⟨a, b⟩
    let resolution := guardedProductEventClassifierResolution
      A B C D hA hB hC hD hE hH left right root
    let depth := guardedProductEventResolutionDepth resolution
    have hsufficient : (2 / 3 : ℚ) ^ (depth + 1) * (b - a) <
        resolution.threshold := by
      simpa only [root, resolution, depth] using
        guardedProductEventResolutionDepth_sufficient hab resolution
    exact (buildAuxiliaryProductPartition?_succeeds_at_root_of_guarded_resolution
      resolution depth hab hsufficient).1

/-- Fully constructive universal auxiliary product formula for two displayed
coprime complex-coordinate pairs. -/
theorem auxiliaryProductFormula_of_coprime_coordinates
    (A B C D : RatPolynomial)
    (hA : A.isZero = false) (hB : B.isZero = false)
    (hC : C.isZero = false) (hD : D.isZero = false)
    (hE : (productNumerator A B C D).isZero = false)
    (hH : (productDenominator A B C D).isZero = false)
    (left : FTA.DenseSquarefree.CoprimeCertificate A B)
    (right : FTA.DenseSquarefree.CoprimeCertificate C D)
    {a b : ℚ} (hab : a < b) :
    AuxiliaryProductFormula A B C D a b :=
  (constructiveAuxiliaryProductPartitionProgram
    A B C D hA hB hC hD hE hH left right).auxiliaryProductFormula hab

/-- Product numerator formed after independently gcd-reducing both factor
pairs. -/
def reducedProductNumerator (A B C D : RatPolynomial) : RatPolynomial :=
  productNumerator
    (reducedNumerator A B) (reducedDenominator A B)
    (reducedNumerator C D) (reducedDenominator C D)

/-- Product denominator formed after independently gcd-reducing both factor
pairs. -/
def reducedProductDenominator (A B C D : RatPolynomial) : RatPolynomial :=
  productDenominator
    (reducedNumerator A B) (reducedDenominator A B)
    (reducedNumerator C D) (reducedDenominator C D)

/-- Independent gcd reduction removes exactly the product of the two common
factors from the real product coordinate. -/
theorem productNumerator_reducedPairs_toPolynomial_identity
    (A B C D : RatPolynomial) :
    (productNumerator A B C D).toPolynomial =
      ((FTA.DenseGCD.symmetricGCD A B *
          FTA.DenseGCD.symmetricGCD C D) *
        reducedProductNumerator A B C D).toPolynomial := by
  let a := reducedNumerator A B
  let b := reducedDenominator A B
  let c := reducedNumerator C D
  let d := reducedDenominator C D
  let g := FTA.DenseGCD.symmetricGCD A B
  let k := FTA.DenseGCD.symmetricGCD C D
  have hA : A.toPolynomial = g.toPolynomial * a.toPolynomial := by
    simpa [g, a, reducedNumerator] using
      FTA.DenseGCD.symmetricLeftFactor_toPolynomial_identity A B
  have hB : B.toPolynomial = g.toPolynomial * b.toPolynomial := by
    simpa [g, b, reducedDenominator] using
      FTA.DenseGCD.symmetricRightFactor_toPolynomial_identity A B
  have hC : C.toPolynomial = k.toPolynomial * c.toPolynomial := by
    simpa [k, c, reducedNumerator] using
      FTA.DenseGCD.symmetricLeftFactor_toPolynomial_identity C D
  have hD : D.toPolynomial = k.toPolynomial * d.toPolynomial := by
    simpa [k, d, reducedDenominator] using
      FTA.DenseGCD.symmetricRightFactor_toPolynomial_identity C D
  simp only [productNumerator, reducedProductNumerator,
    toPolynomial_sub, toPolynomial_mul]
  change A.toPolynomial * C.toPolynomial - B.toPolynomial * D.toPolynomial =
    (g.toPolynomial * k.toPolynomial) *
      (a.toPolynomial * c.toPolynomial - b.toPolynomial * d.toPolynomial)
  rw [hA, hB, hC, hD]
  ring

/-- The analogous exact common-factor identity for the imaginary product
coordinate. -/
theorem productDenominator_reducedPairs_toPolynomial_identity
    (A B C D : RatPolynomial) :
    (productDenominator A B C D).toPolynomial =
      ((FTA.DenseGCD.symmetricGCD A B *
          FTA.DenseGCD.symmetricGCD C D) *
        reducedProductDenominator A B C D).toPolynomial := by
  let a := reducedNumerator A B
  let b := reducedDenominator A B
  let c := reducedNumerator C D
  let d := reducedDenominator C D
  let g := FTA.DenseGCD.symmetricGCD A B
  let k := FTA.DenseGCD.symmetricGCD C D
  have hA : A.toPolynomial = g.toPolynomial * a.toPolynomial := by
    simpa [g, a, reducedNumerator] using
      FTA.DenseGCD.symmetricLeftFactor_toPolynomial_identity A B
  have hB : B.toPolynomial = g.toPolynomial * b.toPolynomial := by
    simpa [g, b, reducedDenominator] using
      FTA.DenseGCD.symmetricRightFactor_toPolynomial_identity A B
  have hC : C.toPolynomial = k.toPolynomial * c.toPolynomial := by
    simpa [k, c, reducedNumerator] using
      FTA.DenseGCD.symmetricLeftFactor_toPolynomial_identity C D
  have hD : D.toPolynomial = k.toPolynomial * d.toPolynomial := by
    simpa [k, d, reducedDenominator] using
      FTA.DenseGCD.symmetricRightFactor_toPolynomial_identity C D
  simp only [productDenominator, reducedProductDenominator,
    toPolynomial_add, toPolynomial_mul]
  change A.toPolynomial * D.toPolynomial + B.toPolynomial * C.toPolynomial =
    (g.toPolynomial * k.toPolynomial) *
      (a.toPolynomial * d.toPolynomial + b.toPolynomial * c.toPolynomial)
  rw [hA, hB, hC, hD]
  ring

theorem reducedProductNumerator_isZero_false
    {A B C D : RatPolynomial}
    (hE : (productNumerator A B C D).isZero = false) :
    (reducedProductNumerator A B C D).isZero = false := by
  cases hred : (reducedProductNumerator A B C D).isZero with
  | false => rfl
  | true =>
      have hredPolynomial :
          (reducedProductNumerator A B C D).toPolynomial = 0 :=
        (toPolynomial_eq_zero_iff_isZero _).2 hred
      have hidentity :=
        productNumerator_reducedPairs_toPolynomial_identity A B C D
      simp only [toPolynomial_mul, hredPolynomial, mul_zero] at hidentity
      exact (toPolynomial_ne_zero_of_isZero_false hE hidentity).elim

theorem reducedProductDenominator_isZero_false
    {A B C D : RatPolynomial}
    (hH : (productDenominator A B C D).isZero = false) :
    (reducedProductDenominator A B C D).isZero = false := by
  cases hred : (reducedProductDenominator A B C D).isZero with
  | false => rfl
  | true =>
      have hredPolynomial :
          (reducedProductDenominator A B C D).toPolynomial = 0 :=
        (toPolynomial_eq_zero_iff_isZero _).2 hred
      have hidentity :=
        productDenominator_reducedPairs_toPolynomial_identity A B C D
      simp only [toPolynomial_mul, hredPolynomial, mul_zero] at hidentity
      exact (toPolynomial_ne_zero_of_isZero_false hH hidentity).elim

/-- Multiplying the two independently gcd-reduced rational-function pairs
produces the same rational function as multiplying the original coordinate
pairs. -/
theorem product_reducedPairs_cross_identity (A B C D : RatPolynomial) :
    (productNumerator A B C D).toPolynomial *
        (reducedProductDenominator A B C D).toPolynomial =
      (reducedProductNumerator A B C D).toPolynomial *
        (productDenominator A B C D).toPolynomial := by
  let a := reducedNumerator A B
  let b := reducedDenominator A B
  let c := reducedNumerator C D
  let d := reducedDenominator C D
  have hAB := reducedPair_cross_identity A B
  have hCD := reducedPair_cross_identity C D
  simp only [reducedProductNumerator, reducedProductDenominator,
    productNumerator, productDenominator, toPolynomial_sub,
    toPolynomial_add, toPolynomial_mul] at hAB hCD ⊢
  change A.toPolynomial * b.toPolynomial =
    B.toPolynomial * a.toPolynomial at hAB
  change C.toPolynomial * d.toPolynomial =
    D.toPolynomial * c.toPolynomial at hCD
  linear_combination
    (C.toPolynomial * c.toPolynomial + D.toPolynomial * d.toPolynomial) * hAB +
    (A.toPolynomial * a.toPolynomial + B.toPolynomial * b.toPolynomial) * hCD

/-- Two nonzero dense polynomial pairs representing the same rational
function have independently gcd-reduced representatives differing by one
nonzero rational scalar. -/
theorem reducedPairs_eq_scale_of_cross
    {P Q R S : RatPolynomial}
    (hP : P.isZero = false) (hQ : Q.isZero = false)
    (hR : R.isZero = false) (hS : S.isZero = false)
    (hcross : P.toPolynomial * S.toPolynomial =
      R.toPolynomial * Q.toPolynomial) :
    ∃ c : ℚ, c ≠ 0 ∧
      reducedNumerator R S = scale c (reducedNumerator P Q) ∧
      reducedDenominator R S = scale c (reducedDenominator P Q) := by
  let n₀ := reducedNumerator P Q
  let d₀ := reducedDenominator P Q
  let n₁ := reducedNumerator R S
  let d₁ := reducedDenominator R S
  let g₀ := FTA.DenseGCD.symmetricGCD P Q
  let g₁ := FTA.DenseGCD.symmetricGCD R S
  have hg₀ : g₀.toPolynomial ≠ 0 := by
    apply toPolynomial_ne_zero_of_isZero_false
    exact FTA.DenseGCD.symmetricGCD_isZero_false (Or.inl hP)
  have hg₁ : g₁.toPolynomial ≠ 0 := by
    apply toPolynomial_ne_zero_of_isZero_false
    exact FTA.DenseGCD.symmetricGCD_isZero_false (Or.inl hR)
  have hPFactor : P.toPolynomial = g₀.toPolynomial * n₀.toPolynomial := by
    simpa [g₀, n₀, reducedNumerator] using
      FTA.DenseGCD.symmetricLeftFactor_toPolynomial_identity P Q
  have hQFactor : Q.toPolynomial = g₀.toPolynomial * d₀.toPolynomial := by
    simpa [g₀, d₀, reducedDenominator] using
      FTA.DenseGCD.symmetricRightFactor_toPolynomial_identity P Q
  have hRFactor : R.toPolynomial = g₁.toPolynomial * n₁.toPolynomial := by
    simpa [g₁, n₁, reducedNumerator] using
      FTA.DenseGCD.symmetricLeftFactor_toPolynomial_identity R S
  have hSFactor : S.toPolynomial = g₁.toPolynomial * d₁.toPolynomial := by
    simpa [g₁, d₁, reducedDenominator] using
      FTA.DenseGCD.symmetricRightFactor_toPolynomial_identity R S
  have hreducedCross : n₀.toPolynomial * d₁.toPolynomial =
      n₁.toPolynomial * d₀.toPolynomial := by
    apply mul_left_cancel₀ (mul_ne_zero hg₀ hg₁)
    calc
      g₀.toPolynomial * g₁.toPolynomial *
          (n₀.toPolynomial * d₁.toPolynomial) =
          (g₀.toPolynomial * n₀.toPolynomial) *
            (g₁.toPolynomial * d₁.toPolynomial) := by ring
      _ = P.toPolynomial * S.toPolynomial := by rw [← hPFactor, ← hSFactor]
      _ = R.toPolynomial * Q.toPolynomial := hcross
      _ = (g₁.toPolynomial * n₁.toPolynomial) *
            (g₀.toPolynomial * d₀.toPolynomial) := by
        rw [← hRFactor, ← hQFactor]
      _ = g₀.toPolynomial * g₁.toPolynomial *
          (n₁.toPolynomial * d₀.toPolynomial) := by ring
  have hcoprime₀ : IsCoprime n₀.toPolynomial d₀.toPolynomial := by
    simpa [n₀, d₀] using (reducedPair_isCoprime hP hQ).symm
  have hcoprime₁ : IsCoprime n₁.toPolynomial d₁.toPolynomial := by
    simpa [n₁, d₁] using (reducedPair_isCoprime hR hS).symm
  have hn₀ : n₀.toPolynomial ≠ 0 := by
    apply toPolynomial_ne_zero_of_isZero_false
    simpa [n₀] using reducedNumerator_isZero_false hP
  have hd₀ : d₀.toPolynomial ≠ 0 := by
    apply toPolynomial_ne_zero_of_isZero_false
    simpa [d₀] using reducedDenominator_isZero_false hQ
  rcases coprimePolynomialPairs_eq_scalar hcoprime₀ hcoprime₁
      hn₀ hd₀ hreducedCross with ⟨c, hc, hnPolynomial, hdPolynomial⟩
  have hnScalePolynomial : n₁.toPolynomial = (scale c n₀).toPolynomial := by
    rw [toPolynomial_scale, hnPolynomial]
  have hdScalePolynomial : d₁.toPolynomial = (scale c d₀).toPolynomial := by
    rw [toPolynomial_scale, hdPolynomial]
  have hnNormalized : n₁.normalize = n₁ := by
    simp [n₁, reducedNumerator]
  have hdNormalized : d₁.normalize = d₁ := by
    simp [d₁, reducedDenominator]
  have hnDense : n₁ = scale c n₀ := by
    have hnormalize := normalize_eq_normalize_of_toPolynomial_eq hnScalePolynomial
    rw [hnNormalized, normalize_scale] at hnormalize
    exact hnormalize
  have hdDense : d₁ = scale c d₀ := by
    have hnormalize := normalize_eq_normalize_of_toPolynomial_eq hdScalePolynomial
    rw [hdNormalized, normalize_scale] at hnormalize
    exact hnormalize
  exact ⟨c, hc, by simpa [n₀, n₁] using hnDense,
    by simpa [d₀, d₁] using hdDense⟩

/-- A coprime displayed pair is changed by executable symmetric
gcd reduction only by one common nonzero rational scalar. -/
theorem reducedPair_eq_scale_of_isCoprime
    {P Q : RatPolynomial}
    (hP : P.isZero = false) (hQ : Q.isZero = false)
    (hcoprime : IsCoprime P.toPolynomial Q.toPolynomial) :
    ∃ c : ℚ, c ≠ 0 ∧
      reducedNumerator P Q = scale c P ∧
      reducedDenominator P Q = scale c Q := by
  let numerator := reducedNumerator P Q
  let denominator := reducedDenominator P Q
  have hcoprimeReduced :
      IsCoprime numerator.toPolynomial denominator.toPolynomial := by
    simpa only [numerator, denominator] using
      (reducedPair_isCoprime hP hQ).symm
  have hPPolynomial : P.toPolynomial ≠ 0 :=
    toPolynomial_ne_zero_of_isZero_false hP
  have hQPolynomial : Q.toPolynomial ≠ 0 :=
    toPolynomial_ne_zero_of_isZero_false hQ
  have hcross : P.toPolynomial * denominator.toPolynomial =
      numerator.toPolynomial * Q.toPolynomial := by
    simpa only [numerator, denominator, mul_comm] using
      reducedPair_cross_identity P Q
  rcases coprimePolynomialPairs_eq_scalar hcoprime hcoprimeReduced
      hPPolynomial hQPolynomial hcross with
    ⟨c, hc, hnPolynomial, hdPolynomial⟩
  have hnScalePolynomial : numerator.toPolynomial =
      (scale c P).toPolynomial := by
    rw [toPolynomial_scale, hnPolynomial]
  have hdScalePolynomial : denominator.toPolynomial =
      (scale c Q).toPolynomial := by
    rw [toPolynomial_scale, hdPolynomial]
  have hnDense : numerator = scale c P := by
    have hnormalize :=
      normalize_eq_normalize_of_toPolynomial_eq hnScalePolynomial
    rw [show numerator.normalize = numerator by
        simp [numerator, reducedNumerator],
      normalize_scale] at hnormalize
    exact hnormalize
  have hdDense : denominator = scale c Q := by
    have hnormalize :=
      normalize_eq_normalize_of_toPolynomial_eq hdScalePolynomial
    rw [show denominator.normalize = denominator by
        simp [denominator, reducedDenominator],
      normalize_scale] at hnormalize
    exact hnormalize
  exact ⟨c, hc, by simpa only [numerator] using hnDense,
    by simpa only [denominator] using hdDense⟩

/-- Multiplying both members of a nonzero dense pair by the same nonzero
polynomial changes its independently gcd-reduced representative by only one
nonzero rational scalar. -/
theorem reducedPairs_commonFactor_eq_scale
    {G P Q : RatPolynomial}
    (hG : G.isZero = false) (hP : P.isZero = false)
    (hQ : Q.isZero = false) :
    ∃ c : ℚ, c ≠ 0 ∧
      reducedNumerator (G * P) (G * Q) =
        scale c (reducedNumerator P Q) ∧
      reducedDenominator (G * P) (G * Q) =
        scale c (reducedDenominator P Q) := by
  have hGP : (G * P).isZero = false := isZero_mul_eq_false hG hP
  have hGQ : (G * Q).isZero = false := isZero_mul_eq_false hG hQ
  apply reducedPairs_eq_scale_of_cross hP hQ hGP hGQ
  simp only [toPolynomial_mul]
  ring

/-! ## Same-sign rescaling of signed chains -/

/-- Scaling two signs by two scalars of the same strict sign preserves their
doubled jump. -/
theorem signJump_mul_mul_of_mul_pos
    {a b x y : ℚ} (hab : 0 < a * b) :
    signJump (a * x) (b * y) = signJump x y := by
  rcases mul_pos_iff.mp hab with ⟨ha, hb⟩ | ⟨ha, hb⟩
  · simp [signJump, ratSign_mul, ratSign_of_pos ha, ratSign_of_pos hb]
  · rw [signJump, signJump, ratSign_mul, ratSign_mul,
      ratSign_of_neg ha, ratSign_of_neg hb]
    simp only [neg_one_mul]
    rw [show -ratSign x - -ratSign y = -(ratSign x - ratSign y) by ring,
      Int.natAbs_neg]

/-- Alternating rescaling by same-sign scalars preserves every adjacent jump
and therefore the complete doubled variation. -/
theorem variation2_alternatingMul_of_mul_pos
    {a b : ℚ} (hab : 0 < a * b) :
    ∀ values : List ℚ,
      variation2 (alternatingMul a b values) = variation2 values
  | [] => rfl
  | [_] => rfl
  | x :: y :: values => by
      simp only [alternatingMul, variation2]
      rw [signJump_mul_mul_of_mul_pos hab]
      exact congrArg (signJump x y + ·)
        (variation2_alternatingMul_of_mul_pos
          (a := b) (b := a) (by simpa [mul_comm] using hab) (y :: values))

/-- Endpoint variation is invariant under same-sign alternating rescaling of
all members of a finite signed chain. -/
theorem endpointVariation2_alternatingScale_of_mul_pos
    (chain : List RatPolynomial) {a b : ℚ} (x : ℚ)
    (hab : 0 < a * b) :
    endpointVariation2 (alternatingScale a b chain) x =
      endpointVariation2 chain x := by
  rw [endpointVariation2, endpointVariation2,
    map_eval_alternatingScale]
  exact variation2_alternatingMul_of_mul_pos hab _

/-- Rescaling the two initial signed-remainder inputs by same-sign nonzero
scalars preserves endpoint variation. -/
theorem endpointVariation2_signedRemainderChain_scale_of_mul_pos
    (p q : RatPolynomial) {a b : ℚ} (x : ℚ)
    (hab : 0 < a * b) :
    endpointVariation2 (signedRemainderChain (scale a p) (scale b q)) x =
      endpointVariation2 (signedRemainderChain p q) x := by
  have ha : a ≠ 0 := left_ne_zero_of_mul hab.ne'
  have hb : b ≠ 0 := right_ne_zero_of_mul hab.ne'
  rw [signedRemainderChain_scale p q ha hb]
  exact endpointVariation2_alternatingScale_of_mul_pos _ x hab

/-- Consequently the endpoint difference computed by a signed chain is
invariant under same-sign rescaling. -/
theorem signedRemainderVariationDifference_scale_of_mul_pos
    (p q : RatPolynomial) {a b : ℚ} (u v : ℚ)
    (hab : 0 < a * b) :
    (endpointVariation2 (signedRemainderChain (scale a p) (scale b q)) u : ℤ) -
        endpointVariation2 (signedRemainderChain (scale a p) (scale b q)) v =
      (endpointVariation2 (signedRemainderChain p q) u : ℤ) -
        endpointVariation2 (signedRemainderChain p q) v := by
  rw [endpointVariation2_signedRemainderChain_scale_of_mul_pos p q u hab,
    endpointVariation2_signedRemainderChain_scale_of_mul_pos p q v hab]

/-- The executable doubled Cauchy index depends only on the represented
rational function: two nonzero polynomial pairs with equal cross products
have the same index on every rational interval. -/
theorem cauchyIndex2_eq_of_cross
    {P Q R S : RatPolynomial}
    (hP : P.isZero = false) (hQ : Q.isZero = false)
    (hR : R.isZero = false) (hS : S.isZero = false)
    (hcross : P.toPolynomial * S.toPolynomial =
      R.toPolynomial * Q.toPolynomial) (a b : ℚ) :
    cauchyIndex2 R S a b = cauchyIndex2 P Q a b := by
  rcases reducedPairs_eq_scale_of_cross hP hQ hR hS hcross with
    ⟨c, hc, hn, hd⟩
  have hcc : 0 < c * c := mul_self_pos.mpr hc
  simp only [cauchyIndex2, hR, hS, hP, hQ, Bool.false_or,
    Bool.false_eq_true, if_false, cauchyChain]
  rw [hn, hd,
    endpointVariation2_signedRemainderChain_scale_of_mul_pos
      (reducedDenominator P Q) (reducedNumerator P Q) a hcc,
    endpointVariation2_signedRemainderChain_scale_of_mul_pos
      (reducedDenominator P Q) (reducedNumerator P Q) b hcc]

/-- For a coprime pair, the executable Cauchy index is the endpoint
difference of its displayed signed remainder chain, without another hidden
change of representatives. -/
theorem cauchyIndex2_eq_raw_of_isCoprime
    {P Q : RatPolynomial}
    (hP : P.isZero = false) (hQ : Q.isZero = false)
    (hcoprime : IsCoprime P.toPolynomial Q.toPolynomial)
    (a b : ℚ) :
    cauchyIndex2 P Q a b =
      (endpointVariation2 (signedRemainderChain Q P) a : ℤ) -
        endpointVariation2 (signedRemainderChain Q P) b := by
  rcases reducedPair_eq_scale_of_isCoprime hP hQ hcoprime with
    ⟨c, hc, hn, hd⟩
  have hcc : 0 < c * c := mul_self_pos.mpr hc
  have hcondition : ¬(P.isZero || Q.isZero) := by simp [hP, hQ]
  rw [cauchyIndex2, if_neg hcondition]
  change
    (endpointVariation2
        (signedRemainderChain (reducedDenominator P Q)
          (reducedNumerator P Q)) a : ℤ) -
      endpointVariation2
        (signedRemainderChain (reducedDenominator P Q)
          (reducedNumerator P Q)) b = _
  rw [hn, hd]
  exact signedRemainderVariationDifference_scale_of_mul_pos
    Q P a b hcc

/-- Independently rescaling numerator and denominator by scalars with the
same strict sign preserves the complete executable Cauchy index.  The proof
passes through the coprime reduced pair, where the signed-chain alternating
rescaling theorem applies directly. -/
theorem cauchyIndex2_scale_of_mul_pos
    {R S : RatPolynomial} (hR : R.isZero = false) (hS : S.isZero = false)
    {c d : ℚ} (hcd : 0 < c * d) (a b : ℚ) :
    cauchyIndex2 (scale c R) (scale d S) a b =
      cauchyIndex2 R S a b := by
  let numerator := reducedNumerator R S
  let denominator := reducedDenominator R S
  have hc : c ≠ 0 := left_ne_zero_of_mul hcd.ne'
  have hd : d ≠ 0 := right_ne_zero_of_mul hcd.ne'
  have hn : numerator.isZero = false := by
    simpa only [numerator] using reducedNumerator_isZero_false hR
  have hden : denominator.isZero = false := by
    simpa only [denominator] using reducedDenominator_isZero_false hS
  have hcn : (scale c numerator).isZero = false := scale_isZero_false hc hn
  have hdd : (scale d denominator).isZero = false :=
    scale_isZero_false hd hden
  have hcR : (scale c R).isZero = false := scale_isZero_false hc hR
  have hdS : (scale d S).isZero = false := scale_isZero_false hd hS
  have hcross : (scale c numerator).toPolynomial *
      (scale d S).toPolynomial =
    (scale c R).toPolynomial * (scale d denominator).toPolynomial := by
    have hreduced := reducedPair_cross_identity R S
    simp only [toPolynomial_scale]
    calc
      Polynomial.C c * numerator.toPolynomial *
            (Polynomial.C d * S.toPolynomial) =
          Polynomial.C c * Polynomial.C d *
            (S.toPolynomial * numerator.toPolynomial) := by ring
      _ = Polynomial.C c * Polynomial.C d *
            (R.toPolynomial * denominator.toPolynomial) := by rw [hreduced]
      _ = Polynomial.C c * R.toPolynomial *
            (Polynomial.C d * denominator.toPolynomial) := by ring
  have hrepresentation :
      cauchyIndex2 (scale c R) (scale d S) a b =
        cauchyIndex2 (scale c numerator) (scale d denominator) a b :=
    cauchyIndex2_eq_of_cross hcn hdd hcR hdS hcross a b
  have hcoprime :
      IsCoprime (scale c numerator).toPolynomial
        (scale d denominator).toPolynomial := by
    simp only [toPolynomial_scale]
    apply (isCoprime_mul_units_left
      (Polynomial.isUnit_C.mpr (isUnit_iff_ne_zero.mpr hc))
      (Polynomial.isUnit_C.mpr (isUnit_iff_ne_zero.mpr hd))
      numerator.toPolynomial denominator.toPolynomial).2
    simpa only [numerator, denominator] using
      (reducedPair_isCoprime hR hS).symm
  have hraw := cauchyIndex2_eq_raw_of_isCoprime
    hcn hdd hcoprime a b
  have hscaled := signedRemainderVariationDifference_scale_of_mul_pos
    denominator numerator (a := d) (b := c) a b
      (by simpa [mul_comm] using hcd)
  have hcondition : ¬(R.isZero || S.isZero) := by simp [hR, hS]
  rw [hrepresentation, hraw, hscaled, cauchyIndex2, if_neg hcondition]
  rfl

/-- Negating the displayed numerator negates the complete executable Cauchy
index.  The proof reduces to the finite signed-chain table saying that the
endpoint sums for second members `P` and `-P` are constant. -/
theorem cauchyIndex2_neg_numerator
    (R S : RatPolynomial) (a b : ℚ)
    (hR : R.isZero = false) (hS : S.isZero = false) :
    cauchyIndex2 (-R) S a b = -cauchyIndex2 R S a b := by
  let numerator := reducedNumerator R S
  let denominator := reducedDenominator R S
  have hn : numerator.isZero = false := by
    simpa only [numerator] using
      (reducedNumerator_isZero_false (R := R) (S := S) hR)
  have hd : denominator.isZero = false := by
    simpa only [denominator] using
      (reducedDenominator_isZero_false (R := R) (S := S) hS)
  have hnegR : (-R).isZero = false := by simpa using hR
  have hnegN : (-numerator).isZero = false := by simpa using hn
  have hcross : (-numerator).toPolynomial * S.toPolynomial =
      (-R).toPolynomial * denominator.toPolynomial := by
    have hreduced := reducedPair_cross_identity R S
    simp only [toPolynomial_neg]
    calc
      -numerator.toPolynomial * S.toPolynomial =
          -(S.toPolynomial * numerator.toPolynomial) := by ring
      _ = -(R.toPolynomial * denominator.toPolynomial) := by
        rw [← hreduced]
      _ = -R.toPolynomial * denominator.toPolynomial := by ring
  have hrepresentation : cauchyIndex2 (-R) S a b =
      cauchyIndex2 (-numerator) denominator a b :=
    cauchyIndex2_eq_of_cross hnegN hd hnegR hS hcross a b
  have hcoprime :
      IsCoprime numerator.toPolynomial denominator.toPolynomial := by
    simpa only [numerator, denominator] using
      (reducedPair_isCoprime hR hS).symm
  have hcoprimeNeg :
      IsCoprime (-numerator).toPolynomial denominator.toPolynomial := by
    simpa only [toPolynomial_neg] using hcoprime.neg_left
  have hrawNeg := cauchyIndex2_eq_raw_of_isCoprime
    hnegN hd hcoprimeNeg a b
  have hcondition : ¬(R.isZero || S.isZero) := by simp [hR, hS]
  have hraw : cauchyIndex2 R S a b =
      (endpointVariation2
          (signedRemainderChain denominator numerator) a : ℤ) -
        endpointVariation2
          (signedRemainderChain denominator numerator) b := by
    rw [cauchyIndex2, if_neg hcondition]
    rfl
  have hnoCommon : NoCommonRationalZero denominator numerator :=
    noCommonRationalZero_of_isCoprime
      (by simpa only [numerator, denominator] using
        reducedPair_isCoprime hR hS)
  have hsum := endpointVariation2_neg_second_sum_eq
    hnoCommon a b
  rw [hrepresentation, hrawNeg, hraw]
  omega

/-- Negating the displayed denominator also negates the complete executable
Cauchy index.  Simultaneous negation is a same-sign rescaling, and numerator
oddness then isolates the denominator sign. -/
theorem cauchyIndex2_neg_denominator
    (R S : RatPolynomial) (a b : ℚ)
    (hR : R.isZero = false) (hS : S.isZero = false) :
    cauchyIndex2 R (-S) a b = -cauchyIndex2 R S a b := by
  have hnegR : (-R).isZero = false := by simpa using hR
  have hnegS : (-S).isZero = false := by simpa using hS
  have hboth := cauchyIndex2_scale_of_mul_pos hR hS
    (c := (-1 : ℚ)) (d := (-1 : ℚ)) (by norm_num) a b
  have hscaleR : scale (-1 : ℚ) R = -R := by
    have hpoly : (scale (-1 : ℚ) R).toPolynomial = (-R).toPolynomial := by
      simp only [toPolynomial_scale, toPolynomial_neg]
      norm_num
    have equality := normalize_eq_normalize_of_toPolynomial_eq hpoly
    rw [normalize_scale, normalize_neg] at equality
    exact equality
  have hscaleS : scale (-1 : ℚ) S = -S := by
    have hpoly : (scale (-1 : ℚ) S).toPolynomial = (-S).toPolynomial := by
      simp only [toPolynomial_scale, toPolynomial_neg]
      norm_num
    have equality := normalize_eq_normalize_of_toPolynomial_eq hpoly
    rw [normalize_scale, normalize_neg] at equality
    exact equality
  rw [hscaleR, hscaleS] at hboth
  have hnegative := cauchyIndex2_neg_numerator R (-S) a b hR hnegS
  omega

/-- Replacing a nonzero pair by its executable gcd-reduced numerator and
denominator preserves the doubled Cauchy index. -/
theorem cauchyIndex2_reducedPair
    {P Q : RatPolynomial} (hP : P.isZero = false) (hQ : Q.isZero = false)
    (a b : ℚ) :
    cauchyIndex2 (reducedNumerator P Q) (reducedDenominator P Q) a b =
      cauchyIndex2 P Q a b := by
  let numerator := reducedNumerator P Q
  let denominator := reducedDenominator P Q
  change cauchyIndex2 numerator denominator a b = cauchyIndex2 P Q a b
  apply cauchyIndex2_eq_of_cross (P := P) (Q := Q)
    (R := numerator) (S := denominator) hP hQ
  · simpa [numerator] using reducedNumerator_isZero_false hP
  · simpa [denominator] using reducedDenominator_isZero_false hQ
  · simpa [numerator, denominator, mul_comm] using
      reducedPair_cross_identity P Q

/-- The product rational function formed from two reduced coordinate pairs
has the same doubled Cauchy index as the product formed before reduction. -/
theorem cauchyIndex2_reducedProduct
    {A B C D : RatPolynomial}
    (hProductNumerator : (productNumerator A B C D).isZero = false)
    (hProductDenominator : (productDenominator A B C D).isZero = false)
    (hReducedNumerator : (reducedProductNumerator A B C D).isZero = false)
    (hReducedDenominator : (reducedProductDenominator A B C D).isZero = false)
    (a b : ℚ) :
    cauchyIndex2 (reducedProductNumerator A B C D)
        (reducedProductDenominator A B C D) a b =
      cauchyIndex2 (productNumerator A B C D)
        (productDenominator A B C D) a b :=
  cauchyIndex2_eq_of_cross hProductNumerator hProductDenominator
    hReducedNumerator hReducedDenominator
    (product_reducedPairs_cross_identity A B C D) a b

/-- The symmetric executable gcd cannot vanish at a rational endpoint where
the represented coordinate pair is nonzero. -/
theorem symmetricGCD_eval_ne_zero_of_pair_ne_zero
    {P Q : RatPolynomial} {x : ℚ}
    (hpair : P.eval x ≠ 0 ∨ Q.eval x ≠ 0) :
    (FTA.DenseGCD.symmetricGCD P Q).eval x ≠ 0 := by
  intro hgcd
  rcases hpair with hP | hQ
  · apply hP
    rw [FTA.DenseGCD.symmetricLeftFactor_eval_identity P Q x,
      hgcd, zero_mul]
  · apply hQ
    rw [FTA.DenseGCD.symmetricRightFactor_eval_identity P Q x,
      hgcd, zero_mul]

/-- A gcd-reduced endpoint variation has the same parity as the explicit flag
recording whether the displayed denominator vanishes.  The original pair
being nonzero makes the symmetric gcd and the terminal signed-chain member
nonzero, so every interior sign cancels. -/
theorem endpointVariation2_cauchyChain_sub_zeroFlag_even
    {R S : RatPolynomial} {x : ℚ}
    (hR : R.isZero = false) (hS : S.isZero = false)
    (hpair : R.eval x ≠ 0 ∨ S.eval x ≠ 0) :
    Even (((endpointVariation2 (cauchyChain R S) x : ℕ) : ℤ) -
      (if S.eval x = 0 then 1 else 0)) := by
  let numerator := reducedNumerator R S
  let denominator := reducedDenominator R S
  have hn : numerator.isZero = false := by
    simpa only [numerator] using reducedNumerator_isZero_false hR
  have hcoprime : NoCommonRationalZero denominator numerator := by
    simpa only [denominator, numerator] using
      noCommonRationalZero_of_isCoprime (reducedPair_isCoprime hR hS)
  obtain ⟨tail, hchain⟩ :=
    signedRemainderChain_eq_cons denominator numerator
  have hterminal :
      terminalValue (denominator.eval x)
          (tail.map fun p => p.eval x) ≠ 0 :=
    terminalValue_signedRemainderChain_eval_ne_zero
      hn hcoprime x hchain
  have hgcd : (FTA.DenseGCD.symmetricGCD R S).eval x ≠ 0 :=
    symmetricGCD_eval_ne_zero_of_pair_ne_zero hpair
  have hdenominatorZero : denominator.eval x = 0 ↔ S.eval x = 0 := by
    constructor
    · intro hd
      rw [FTA.DenseGCD.symmetricRightFactor_eval_identity R S x]
      change (FTA.DenseGCD.symmetricGCD R S).eval x *
          denominator.eval x = 0
      rw [hd, mul_zero]
    · intro hSx
      have hproduct := FTA.DenseGCD.symmetricRightFactor_eval_identity R S x
      rw [hSx] at hproduct
      exact (mul_eq_zero.mp hproduct.symm).resolve_left hgcd
  have hvariation := variation2_sub_signDifference_even
    (denominator.eval x) (tail.map fun p => p.eval x)
  have hfirstToFlag :
      Even ((ratSign (denominator.eval x) -
        ratSign (terminalValue (denominator.eval x)
          (tail.map fun p => p.eval x))) -
        (if S.eval x = 0 then 1 else 0)) := by
    have hbase := ratSign_sub_terminal_sub_zeroFlag_even
      (x := denominator.eval x) hterminal
    by_cases hSx : S.eval x = 0
    · have hd : denominator.eval x = 0 := hdenominatorZero.mpr hSx
      simpa [hSx, hd] using hbase
    · have hd : denominator.eval x ≠ 0 :=
        fun hzero => hSx (hdenominatorZero.mp hzero)
      simpa [hSx, hd] using hbase
  rcases hvariation.add hfirstToFlag with ⟨k, hk⟩
  rw [endpointVariation2, cauchyChain, show
    signedRemainderChain (reducedDenominator R S)
        (reducedNumerator R S) = denominator :: tail by
      simpa only [denominator, numerator] using hchain]
  simp only [List.map_cons]
  refine ⟨k, ?_⟩
  calc
    ((variation2 (denominator.eval x :: tail.map fun p => p.eval x) : ℕ) : ℤ) -
        (if S.eval x = 0 then 1 else 0) =
        (((variation2 (denominator.eval x :: tail.map fun p => p.eval x) : ℕ) : ℤ) -
          (ratSign (denominator.eval x) -
            ratSign (terminalValue (denominator.eval x)
              (tail.map fun p => p.eval x)))) +
        ((ratSign (denominator.eval x) -
            ratSign (terminalValue (denominator.eval x)
              (tail.map fun p => p.eval x))) -
          (if S.eval x = 0 then 1 else 0)) := by ring
    _ = k + k := hk

/-- The doubled Cauchy index has the same parity as the difference of its two
denominator-zero flags.  This includes identically-zero coordinate rows,
where endpoint nonvanishing forces the two flags to cancel. -/
theorem cauchyIndex2_sub_endpointFlags_even
    {R S : RatPolynomial} {a b : ℚ}
    (ha : R.eval a ≠ 0 ∨ S.eval a ≠ 0)
    (hb : R.eval b ≠ 0 ∨ S.eval b ≠ 0) :
    Even (cauchyIndex2 R S a b -
      ((if S.eval a = 0 then 1 else 0) -
        (if S.eval b = 0 then 1 else 0))) := by
  by_cases hRZero : R.isZero = true
  · have hRa := eval_eq_zero_of_isZero hRZero a
    have hRb := eval_eq_zero_of_isZero hRZero b
    have hSa : S.eval a ≠ 0 := ha.resolve_left (fun h => h hRa)
    have hSb : S.eval b ≠ 0 := hb.resolve_left (fun h => h hRb)
    exact ⟨0, by simp [cauchyIndex2, hRZero, hSa, hSb]⟩
  have hR : R.isZero = false := by simpa using hRZero
  by_cases hSZero : S.isZero = true
  · have hSa := eval_eq_zero_of_isZero hSZero a
    have hSb := eval_eq_zero_of_isZero hSZero b
    exact ⟨0, by simp [cauchyIndex2, hSZero, hSa, hSb]⟩
  have hS : S.isZero = false := by simpa using hSZero
  have hcondition : ¬(R.isZero || S.isZero) := by simp [hR, hS]
  have haEven := endpointVariation2_cauchyChain_sub_zeroFlag_even hR hS ha
  have hbEven := endpointVariation2_cauchyChain_sub_zeroFlag_even hR hS hb
  rcases haEven.sub hbEven with ⟨k, hk⟩
  refine ⟨k, ?_⟩
  rw [cauchyIndex2, if_neg hcondition]
  calc
    ((endpointVariation2 (cauchyChain R S) a : ℕ) : ℤ) -
          ((endpointVariation2 (cauchyChain R S) b : ℕ) : ℤ) -
        ((if S.eval a = 0 then 1 else 0) -
          (if S.eval b = 0 then 1 else 0)) =
        ((((endpointVariation2 (cauchyChain R S) a : ℕ) : ℤ) -
          (if S.eval a = 0 then 1 else 0)) -
        (((endpointVariation2 (cauchyChain R S) b : ℕ) : ℤ) -
          (if S.eval b = 0 then 1 else 0))) := by ring
    _ = k + k := hk

/-- At every point where the displayed pair is nonzero, the first two-entry
jump of the gcd-reduced Cauchy chain is exactly the raw endpoint jump used by
the product formula. -/
theorem pairEndpointVariation2_eq_raw_product_jump
    {R S : RatPolynomial} {x : ℚ}
    (hR : R.isZero = false) (hS : S.isZero = false)
    (hpair : R.eval x ≠ 0 ∨ S.eval x ≠ 0) :
    pairEndpointVariation2 R S x =
      signJump 1 (R.eval x * S.eval x) := by
  let g := FTA.DenseGCD.symmetricGCD R S
  let numerator := reducedNumerator R S
  let denominator := reducedDenominator R S
  have hcoprime : NoCommonRationalZero denominator numerator :=
    noCommonRationalZero_of_isCoprime (reducedPair_isCoprime hR hS)
  have hreducedNonzero : denominator.eval x ≠ 0 ∨ numerator.eval x ≠ 0 := by
    by_contra hzero
    rw [not_or, not_ne_iff, not_ne_iff] at hzero
    exact hcoprime x ⟨hzero.1, hzero.2⟩
  have hfinite := FiniteSign.jump_eq_positive_mul
    (FiniteSign.ofRat (denominator.eval x))
    (FiniteSign.ofRat (numerator.eval x))
    (by simpa [FiniteSign.ofRat_eq_zero_iff] using hreducedNonzero)
  have hjump : signJump (denominator.eval x) (numerator.eval x) =
      signJump 1 (denominator.eval x * numerator.eval x) := by
    rw [← FiniteSign.ofRat_mul] at hfinite
    have hpositive : FiniteSign.positive = FiniteSign.ofRat 1 := rfl
    rw [hpositive] at hfinite
    simpa only [FiniteSign.jump_ofRat] using hfinite
  have hg : g.eval x ≠ 0 :=
    symmetricGCD_eval_ne_zero_of_pair_ne_zero hpair
  have hRFactor : R.eval x = g.eval x * numerator.eval x := by
    simpa only [g, numerator, reducedNumerator] using
      FTA.DenseGCD.symmetricLeftFactor_eval_identity R S x
  have hSFactor : S.eval x = g.eval x * denominator.eval x := by
    simpa only [g, denominator, reducedDenominator] using
      FTA.DenseGCD.symmetricRightFactor_eval_identity R S x
  have hargument : R.eval x * S.eval x =
      g.eval x ^ 2 * (denominator.eval x * numerator.eval x) := by
    rw [hRFactor, hSFactor]
    ring
  have hscale : 0 < (1 : ℚ) * g.eval x ^ 2 := by
    simpa using sq_pos_of_ne_zero hg
  have hscaled := signJump_mul_mul_of_mul_pos
    (a := (1 : ℚ)) (b := g.eval x ^ 2)
    (x := (1 : ℚ))
    (y := denominator.eval x * numerator.eval x) hscale
  unfold pairEndpointVariation2
  rw [hjump, hargument]
  simpa only [one_mul] using hscaled.symm

theorem pairVariationDifference2_eq_raw_product_jumps
    {R S : RatPolynomial} {a b : ℚ}
    (hR : R.isZero = false) (hS : S.isZero = false)
    (ha : R.eval a ≠ 0 ∨ S.eval a ≠ 0)
    (hb : R.eval b ≠ 0 ∨ S.eval b ≠ 0) :
    pairVariationDifference2 R S a b =
      (signJump 1 (R.eval a * S.eval a) : ℤ) -
        signJump 1 (R.eval b * S.eval b) := by
  rw [pairVariationDifference2,
    pairEndpointVariation2_eq_raw_product_jump hR hS ha,
    pairEndpointVariation2_eq_raw_product_jump hR hS hb]

/-- The endpoint correction is unchanged by independently gcd-reducing both
coordinate pairs, because the two removed gcd values occur only through a
strictly positive square. -/
theorem auxiliaryEndpointCorrection2_reducedPairs
    (A B C D : RatPolynomial) (x : ℚ)
    (hleft : A.eval x ≠ 0 ∨ B.eval x ≠ 0)
    (hright : C.eval x ≠ 0 ∨ D.eval x ≠ 0) :
    auxiliaryEndpointCorrection2 A B C D x =
      auxiliaryEndpointCorrection2
        (reducedNumerator A B) (reducedDenominator A B)
        (reducedNumerator C D) (reducedDenominator C D) x := by
  let a := reducedNumerator A B
  let b := reducedDenominator A B
  let c := reducedNumerator C D
  let d := reducedDenominator C D
  let g := FTA.DenseGCD.symmetricGCD A B
  let k := FTA.DenseGCD.symmetricGCD C D
  have hg : g.eval x ≠ 0 := by
    exact symmetricGCD_eval_ne_zero_of_pair_ne_zero hleft
  have hk : k.eval x ≠ 0 := by
    exact symmetricGCD_eval_ne_zero_of_pair_ne_zero hright
  have hA : A.eval x = g.eval x * a.eval x := by
    simpa [g, a, reducedNumerator] using
      FTA.DenseGCD.symmetricLeftFactor_eval_identity A B x
  have hB : B.eval x = g.eval x * b.eval x := by
    simpa [g, b, reducedDenominator] using
      FTA.DenseGCD.symmetricRightFactor_eval_identity A B x
  have hC : C.eval x = k.eval x * c.eval x := by
    simpa [k, c, reducedNumerator] using
      FTA.DenseGCD.symmetricLeftFactor_eval_identity C D x
  have hD : D.eval x = k.eval x * d.eval x := by
    simpa [k, d, reducedDenominator] using
      FTA.DenseGCD.symmetricRightFactor_eval_identity C D x
  have hscale : 0 < g.eval x ^ 2 * k.eval x ^ 2 :=
    mul_pos (sq_pos_of_ne_zero hg) (sq_pos_of_ne_zero hk)
  have hargument :
      (A.eval x * D.eval x + B.eval x * C.eval x) *
          (B.eval x * D.eval x) =
        (g.eval x ^ 2 * k.eval x ^ 2) *
          ((a.eval x * d.eval x + b.eval x * c.eval x) *
            (b.eval x * d.eval x)) := by
    rw [hA, hB, hC, hD]
    ring
  rw [auxiliaryEndpointCorrection2_eq_signJump,
    auxiliaryEndpointCorrection2_eq_signJump]
  apply signJump_congr rfl
  rw [hargument, ratSign_mul, ratSign_of_pos hscale, one_mul]

/-- In the nondegenerate coordinate case, proving the auxiliary product
formula after independent gcd reduction proves it for the original pairs.
The four endpoint hypotheses are exactly the paper's vertex nonvanishing
condition at the two ends of the oriented cell. -/
theorem auxiliaryProductFormula_of_reducedPairs
    {A B C D : RatPolynomial} {a b : ℚ}
    (hA : A.isZero = false) (hB : B.isZero = false)
    (hC : C.isZero = false) (hD : D.isZero = false)
    (hProductNumerator : (productNumerator A B C D).isZero = false)
    (hProductDenominator : (productDenominator A B C D).isZero = false)
    (hReducedProductNumerator :
      (reducedProductNumerator A B C D).isZero = false)
    (hReducedProductDenominator :
      (reducedProductDenominator A B C D).isZero = false)
    (hleftA : A.eval a ≠ 0 ∨ B.eval a ≠ 0)
    (hleftC : C.eval a ≠ 0 ∨ D.eval a ≠ 0)
    (hrightA : A.eval b ≠ 0 ∨ B.eval b ≠ 0)
    (hrightC : C.eval b ≠ 0 ∨ D.eval b ≠ 0)
    (hreduced : AuxiliaryProductFormula
      (reducedNumerator A B) (reducedDenominator A B)
      (reducedNumerator C D) (reducedDenominator C D) a b) :
    AuxiliaryProductFormula A B C D a b := by
  rw [AuxiliaryProductFormula] at hreduced ⊢
  change cauchyIndex2 (reducedProductNumerator A B C D)
      (reducedProductDenominator A B C D) a b =
    cauchyIndex2 (reducedNumerator A B) (reducedDenominator A B) a b +
      cauchyIndex2 (reducedNumerator C D) (reducedDenominator C D) a b -
      (auxiliaryEndpointCorrection2
        (reducedNumerator A B) (reducedDenominator A B)
        (reducedNumerator C D) (reducedDenominator C D) a : ℤ) +
      auxiliaryEndpointCorrection2
        (reducedNumerator A B) (reducedDenominator A B)
        (reducedNumerator C D) (reducedDenominator C D) b at hreduced
  rw [cauchyIndex2_reducedProduct hProductNumerator hProductDenominator
      hReducedProductNumerator hReducedProductDenominator a b,
    cauchyIndex2_reducedPair hA hB a b,
    cauchyIndex2_reducedPair hC hD a b,
    ← auxiliaryEndpointCorrection2_reducedPairs A B C D a hleftA hleftC,
    ← auxiliaryEndpointCorrection2_reducedPairs A B C D b hrightA hrightC]
    at hreduced
  exact hreduced

/-- A total partition program for the two gcd-reduced coordinate pairs
therefore proves the original auxiliary product formula on every proper cell
with nonzero factor endpoints. -/
theorem auxiliaryProductFormula_of_reducedPartitionProgram
    {A B C D : RatPolynomial} {a b : ℚ}
    (hA : A.isZero = false) (hB : B.isZero = false)
    (hC : C.isZero = false) (hD : D.isZero = false)
    (hProductNumerator : (productNumerator A B C D).isZero = false)
    (hProductDenominator : (productDenominator A B C D).isZero = false)
    (hReducedProductNumerator :
      (reducedProductNumerator A B C D).isZero = false)
    (hReducedProductDenominator :
      (reducedProductDenominator A B C D).isZero = false)
    (hleftA : A.eval a ≠ 0 ∨ B.eval a ≠ 0)
    (hleftC : C.eval a ≠ 0 ∨ D.eval a ≠ 0)
    (hrightA : A.eval b ≠ 0 ∨ B.eval b ≠ 0)
    (hrightC : C.eval b ≠ 0 ∨ D.eval b ≠ 0)
    (hab : a < b)
    (program : AuxiliaryProductPartitionProgram
      (reducedNumerator A B) (reducedDenominator A B)
      (reducedNumerator C D) (reducedDenominator C D)) :
    AuxiliaryProductFormula A B C D a b :=
  auxiliaryProductFormula_of_reducedPairs hA hB hC hD
    hProductNumerator hProductDenominator hReducedProductNumerator
    hReducedProductDenominator hleftA hleftC hrightA hrightC
    (program.auxiliaryProductFormula hab)

/-- The completed finite partition construction, followed by exact gcd
transfer, proves the auxiliary product formula for arbitrary nondegenerate
displayed coordinates.  Only the paper's factor nonvanishing conditions at
the two rational endpoints remain. -/
theorem auxiliaryProductFormula_of_nonzero_coordinates
    {A B C D : RatPolynomial} {a b : ℚ}
    (hA : A.isZero = false) (hB : B.isZero = false)
    (hC : C.isZero = false) (hD : D.isZero = false)
    (hE : (productNumerator A B C D).isZero = false)
    (hH : (productDenominator A B C D).isZero = false)
    (hleftA : A.eval a ≠ 0 ∨ B.eval a ≠ 0)
    (hleftC : C.eval a ≠ 0 ∨ D.eval a ≠ 0)
    (hrightA : A.eval b ≠ 0 ∨ B.eval b ≠ 0)
    (hrightC : C.eval b ≠ 0 ∨ D.eval b ≠ 0)
    (hab : a < b) :
    AuxiliaryProductFormula A B C D a b := by
  have hReducedA := reducedNumerator_isZero_false
    (R := A) (S := B) hA
  have hReducedB := reducedDenominator_isZero_false
    (R := A) (S := B) hB
  have hReducedC := reducedNumerator_isZero_false
    (R := C) (S := D) hC
  have hReducedD := reducedDenominator_isZero_false
    (R := C) (S := D) hD
  have hReducedE := reducedProductNumerator_isZero_false hE
  have hReducedH := reducedProductDenominator_isZero_false hH
  let leftCertificate :=
    (FTA.SturmTransducer.reducedCauchyPairCertificate A B hA hB).swap
  let rightCertificate :=
    (FTA.SturmTransducer.reducedCauchyPairCertificate C D hC hD).swap
  have hreduced : AuxiliaryProductFormula
      (reducedNumerator A B) (reducedDenominator A B)
      (reducedNumerator C D) (reducedDenominator C D) a b := by
    apply auxiliaryProductFormula_of_coprime_coordinates
      (reducedNumerator A B) (reducedDenominator A B)
      (reducedNumerator C D) (reducedDenominator C D)
      hReducedA hReducedB hReducedC hReducedD
    · simpa only [reducedProductNumerator] using hReducedE
    · simpa only [reducedProductDenominator] using hReducedH
    · exact leftCertificate
    · exact rightCertificate
    · exact hab
  exact auxiliaryProductFormula_of_reducedPairs
    hA hB hC hD hE hH hReducedE hReducedH
    hleftA hleftC hrightA hrightC hreduced

/-- Oriented version of the completed nondegenerate formula.  A decreasing
parameter interval is handled by constructing the increasing partition and
using exact reversal. -/
theorem auxiliaryProductFormula_of_nonzero_coordinates_of_ne
    {A B C D : RatPolynomial} {a b : ℚ}
    (hA : A.isZero = false) (hB : B.isZero = false)
    (hC : C.isZero = false) (hD : D.isZero = false)
    (hE : (productNumerator A B C D).isZero = false)
    (hH : (productDenominator A B C D).isZero = false)
    (hleftA : A.eval a ≠ 0 ∨ B.eval a ≠ 0)
    (hleftC : C.eval a ≠ 0 ∨ D.eval a ≠ 0)
    (hrightA : A.eval b ≠ 0 ∨ B.eval b ≠ 0)
    (hrightC : C.eval b ≠ 0 ∨ D.eval b ≠ 0)
    (hab : a ≠ b) :
    AuxiliaryProductFormula A B C D a b := by
  rcases lt_or_gt_of_ne hab with hlt | hgt
  · exact auxiliaryProductFormula_of_nonzero_coordinates
      hA hB hC hD hE hH hleftA hleftC hrightA hrightC hlt
  · exact (auxiliaryProductFormula_of_nonzero_coordinates
      hA hB hC hD hE hH hrightA hrightC hleftA hleftC hgt).reverse

/-- Universal common-factor invariance of the executable doubled Cauchy
index.  This discharges the gcd-cancellation prerequisite of the product
formula without referring to roots. -/
theorem cauchyIndex2_commonFactor
    {G P Q : RatPolynomial}
    (hG : G.isZero = false) (hP : P.isZero = false)
    (hQ : Q.isZero = false) (a b : ℚ) :
    cauchyIndex2 (G * P) (G * Q) a b = cauchyIndex2 P Q a b := by
  have hGP : (G * P).isZero = false := isZero_mul_eq_false hG hP
  have hGQ : (G * Q).isZero = false := isZero_mul_eq_false hG hQ
  apply cauchyIndex2_eq_of_cross hP hQ hGP hGQ
  simp only [toPolynomial_mul]
  ring

/-- The auxiliary product identity is symmetric in its two complex factors. -/
theorem auxiliaryProductFormula_swap
    (A B C D : RatPolynomial) (a b : ℚ) :
    AuxiliaryProductFormula A B C D a b ↔
      AuxiliaryProductFormula C D A B a b := by
  have hE : productNumerator C D A B = productNumerator A B C D := by
    have hpoly : (productNumerator C D A B).toPolynomial =
        (productNumerator A B C D).toPolynomial := by
      simp only [productNumerator, toPolynomial_sub, toPolynomial_mul]
      ring
    simpa [productNumerator] using
      normalize_eq_normalize_of_toPolynomial_eq hpoly
  have hH : productDenominator C D A B =
      productDenominator A B C D := by
    have hpoly : (productDenominator C D A B).toPolynomial =
        (productDenominator A B C D).toPolynomial := by
      simp only [productDenominator, toPolynomial_add, toPolynomial_mul]
      ring
    simpa [productDenominator] using
      normalize_eq_normalize_of_toPolynomial_eq hpoly
  have hcorrection : ∀ x : ℚ,
      auxiliaryEndpointCorrection2 C D A B x =
        auxiliaryEndpointCorrection2 A B C D x := by
    intro x
    rw [auxiliaryEndpointCorrection2_eq_signJump,
      auxiliaryEndpointCorrection2_eq_signJump]
    congr 2
    all_goals ring
  constructor
  · intro h
    unfold AuxiliaryProductFormula at h ⊢
    rw [hE, hH, hcorrection a, hcorrection b]
    omega
  · intro h
    unfold AuxiliaryProductFormula at h ⊢
    rw [hE, hH, hcorrection a, hcorrection b] at h
    omega

/-- Degenerate row with an identically zero first imaginary coordinate.
Both product coordinates have the first real coordinate as a common factor,
and the raw endpoint correction is constant. -/
theorem auxiliaryProductFormula_of_leftImaginary_zero
    {A B C D : RatPolynomial} {a b : ℚ}
    (hB : B.isZero = true)
    (hleftA : A.eval a ≠ 0 ∨ B.eval a ≠ 0)
    (_hleftC : C.eval a ≠ 0 ∨ D.eval a ≠ 0)
    (_hrightA : A.eval b ≠ 0 ∨ B.eval b ≠ 0)
    (_hrightC : C.eval b ≠ 0 ∨ D.eval b ≠ 0) :
    AuxiliaryProductFormula A B C D a b := by
  have hBa : B.eval a = 0 := eval_eq_zero_of_isZero hB a
  have hBb : B.eval b = 0 := eval_eq_zero_of_isZero hB b
  have hAa : A.eval a ≠ 0 := by
    rcases hleftA with hAa | hBaNe
    · exact hAa
    · exact (hBaNe hBa).elim
  have hA : A.isZero = false := isZero_false_of_eval_ne_zero hAa
  by_cases hCZero : C.isZero = true
  · have hCa := eval_eq_zero_of_isZero hCZero a
    have hCb := eval_eq_zero_of_isZero hCZero b
    have hEZero : (productNumerator A B C D).isZero = true := by
      apply (toPolynomial_eq_zero_iff_isZero _).1
      have hBPolynomial := (toPolynomial_eq_zero_iff_isZero B).2 hB
      have hCPolynomial := (toPolynomial_eq_zero_iff_isZero C).2 hCZero
      simp [productNumerator, toPolynomial_sub, toPolynomial_mul,
        hBPolynomial, hCPolynomial]
    simp [AuxiliaryProductFormula, cauchyIndex2, hB, hCZero, hEZero,
      auxiliaryEndpointCorrection2_eq_signJump,
      hBa, hBb, hCa, hCb]
  · have hC : C.isZero = false := by simpa using hCZero
    by_cases hDZero : D.isZero = true
    · have hDa := eval_eq_zero_of_isZero hDZero a
      have hDb := eval_eq_zero_of_isZero hDZero b
      have hHZero : (productDenominator A B C D).isZero = true := by
        apply (toPolynomial_eq_zero_iff_isZero _).1
        have hBPolynomial := (toPolynomial_eq_zero_iff_isZero B).2 hB
        have hDPolynomial := (toPolynomial_eq_zero_iff_isZero D).2 hDZero
        simp [productDenominator, toPolynomial_add, toPolynomial_mul,
          hBPolynomial, hDPolynomial]
      simp [AuxiliaryProductFormula, cauchyIndex2, hB, hDZero, hHZero,
        auxiliaryEndpointCorrection2_eq_signJump,
        hBa, hBb, hDa, hDb]
    · have hD : D.isZero = false := by simpa using hDZero
      have hBPolynomial := (toPolynomial_eq_zero_iff_isZero B).2 hB
      have hAPolynomial := toPolynomial_ne_zero_of_isZero_false hA
      have hCPolynomial := toPolynomial_ne_zero_of_isZero_false hC
      have hDPolynomial := toPolynomial_ne_zero_of_isZero_false hD
      have hE : (productNumerator A B C D).isZero = false := by
        apply isZero_false_of_toPolynomial_ne_zero
        simp only [productNumerator, toPolynomial_sub, toPolynomial_mul,
          hBPolynomial, zero_mul, sub_zero]
        exact mul_ne_zero hAPolynomial hCPolynomial
      have hH : (productDenominator A B C D).isZero = false := by
        apply isZero_false_of_toPolynomial_ne_zero
        simp only [productDenominator, toPolynomial_add, toPolynomial_mul,
          hBPolynomial, zero_mul, add_zero]
        exact mul_ne_zero hAPolynomial hDPolynomial
      have hcross : C.toPolynomial *
          (productDenominator A B C D).toPolynomial =
        (productNumerator A B C D).toPolynomial * D.toPolynomial := by
        simp only [productNumerator, productDenominator, toPolynomial_sub,
          toPolynomial_add, toPolynomial_mul, hBPolynomial, zero_mul,
          sub_zero, add_zero]
        ring
      have hproductIndex :
          cauchyIndex2 (productNumerator A B C D)
              (productDenominator A B C D) a b =
            cauchyIndex2 C D a b :=
        cauchyIndex2_eq_of_cross hC hD hE hH hcross a b
      have hcorrection : ∀ x : ℚ,
          auxiliaryEndpointCorrection2 A B C D x = 1 := by
        intro x
        have hBx : B.eval x = 0 := eval_eq_zero_of_isZero hB x
        simp [auxiliaryEndpointCorrection2_eq_signJump, hBx, signJump,
          ratSign_of_pos (show (0 : ℚ) < 1 by norm_num)]
      unfold AuxiliaryProductFormula
      rw [hproductIndex, hcorrection a, hcorrection b]
      rw [show cauchyIndex2 A B a b = 0 by simp [cauchyIndex2, hB]]
      omega

/-- Degenerate row with an identically zero first real coordinate.  The
nontrivial subcase is exactly Cauchy inversion plus oddness of the numerator;
the endpoint correction is the raw reduced-pair jump after removing the
strictly positive square of the remaining first coordinate. -/
theorem auxiliaryProductFormula_of_leftReal_zero
    {A B C D : RatPolynomial} {a b : ℚ}
    (hA : A.isZero = true) (hB : B.isZero = false)
    (hD : D.isZero = false)
    (hleftA : A.eval a ≠ 0 ∨ B.eval a ≠ 0)
    (hleftC : C.eval a ≠ 0 ∨ D.eval a ≠ 0)
    (hrightA : A.eval b ≠ 0 ∨ B.eval b ≠ 0)
    (hrightC : C.eval b ≠ 0 ∨ D.eval b ≠ 0) :
    AuxiliaryProductFormula A B C D a b := by
  have hAPolynomial : A.toPolynomial = 0 :=
    (toPolynomial_eq_zero_iff_isZero A).2 hA
  by_cases hCZero : C.isZero = true
  · have hCPolynomial : C.toPolynomial = 0 :=
      (toPolynomial_eq_zero_iff_isZero C).2 hCZero
    have hHZero : (productDenominator A B C D).isZero = true := by
      apply (toPolynomial_eq_zero_iff_isZero _).1
      simp [productDenominator, toPolynomial_add, toPolynomial_mul,
        hAPolynomial, hCPolynomial]
    have hAa := eval_eq_zero_of_isZero hA a
    have hAb := eval_eq_zero_of_isZero hA b
    have hCa := eval_eq_zero_of_isZero hCZero a
    have hCb := eval_eq_zero_of_isZero hCZero b
    simp [AuxiliaryProductFormula, cauchyIndex2, hA, hCZero, hHZero,
      auxiliaryEndpointCorrection2_eq_signJump,
      hAa, hAb, hCa, hCb]
  · have hC : C.isZero = false := by simpa using hCZero
    have hBPolynomial := toPolynomial_ne_zero_of_isZero_false hB
    have hCPolynomial := toPolynomial_ne_zero_of_isZero_false hC
    have hDPolynomial := toPolynomial_ne_zero_of_isZero_false hD
    have hE : (productNumerator A B C D).isZero = false := by
      apply isZero_false_of_toPolynomial_ne_zero
      simp only [productNumerator, toPolynomial_sub, toPolynomial_mul,
        hAPolynomial, zero_mul, zero_sub]
      exact neg_ne_zero.mpr (mul_ne_zero hBPolynomial hDPolynomial)
    have hH : (productDenominator A B C D).isZero = false := by
      apply isZero_false_of_toPolynomial_ne_zero
      simp only [productDenominator, toPolynomial_add, toPolynomial_mul,
        hAPolynomial, zero_mul, zero_add]
      exact mul_ne_zero hBPolynomial hCPolynomial
    have hnegD : (-D).isZero = false := by simpa using hD
    have hcross : (-D).toPolynomial *
        (productDenominator A B C D).toPolynomial =
      (productNumerator A B C D).toPolynomial * C.toPolynomial := by
      simp only [productNumerator, productDenominator, toPolynomial_neg,
        toPolynomial_sub, toPolynomial_add, toPolynomial_mul, hAPolynomial,
        zero_mul, zero_sub, zero_add]
      ring
    have hproductIndex :
        cauchyIndex2 (productNumerator A B C D)
            (productDenominator A B C D) a b =
          cauchyIndex2 (-D) C a b :=
      cauchyIndex2_eq_of_cross hnegD hC hE hH hcross a b
    have hnegative := cauchyIndex2_neg_numerator D C a b hD hC
    have hinversion := cauchyIndex2_inversion C D a b hC hD
    have hpairDifference :=
      pairVariationDifference2_eq_raw_product_jumps
        hC hD hleftC hrightC
    have hcorrection : ∀ x : ℚ,
        (A.eval x ≠ 0 ∨ B.eval x ≠ 0) →
        auxiliaryEndpointCorrection2 A B C D x =
          signJump 1 (C.eval x * D.eval x) := by
      intro x hfactor
      have hAx : A.eval x = 0 := eval_eq_zero_of_isZero hA x
      have hBx : B.eval x ≠ 0 := by
        rcases hfactor with hAxNe | hBx
        · exact (hAxNe hAx).elim
        · exact hBx
      have hscale : 0 < (1 : ℚ) * B.eval x ^ 2 := by
        simpa using sq_pos_of_ne_zero hBx
      have hscaled := signJump_mul_mul_of_mul_pos
        (a := (1 : ℚ)) (b := B.eval x ^ 2)
        (x := (1 : ℚ)) (y := C.eval x * D.eval x) hscale
      rw [auxiliaryEndpointCorrection2_eq_signJump, hAx]
      have hargument :
          (0 * D.eval x + B.eval x * C.eval x) *
              (B.eval x * D.eval x) =
            B.eval x ^ 2 * (C.eval x * D.eval x) := by ring
      rw [hargument]
      simpa only [one_mul] using hscaled
    unfold AuxiliaryProductFormula
    rw [hpairDifference] at hinversion
    rw [hproductIndex, hcorrection a hleftA,
      hcorrection b hrightA, hnegative]
    rw [show cauchyIndex2 A B a b = 0 by simp [cauchyIndex2, hA]]
    omega

/-- Symmetric degenerate row with an identically zero second real
coordinate. -/
theorem auxiliaryProductFormula_of_rightReal_zero
    {A B C D : RatPolynomial} {a b : ℚ}
    (hC : C.isZero = true) (hD : D.isZero = false)
    (hB : B.isZero = false)
    (hleftA : A.eval a ≠ 0 ∨ B.eval a ≠ 0)
    (hleftC : C.eval a ≠ 0 ∨ D.eval a ≠ 0)
    (hrightA : A.eval b ≠ 0 ∨ B.eval b ≠ 0)
    (hrightC : C.eval b ≠ 0 ∨ D.eval b ≠ 0) :
    AuxiliaryProductFormula A B C D a b :=
  (auxiliaryProductFormula_swap A B C D a b).mpr
    (auxiliaryProductFormula_of_leftReal_zero
      hC hD hB hleftC hleftA hrightC hrightA)

/-- Symmetric degenerate row with an identically zero second imaginary
coordinate. -/
theorem auxiliaryProductFormula_of_rightImaginary_zero
    {A B C D : RatPolynomial} {a b : ℚ}
    (hD : D.isZero = true)
    (hleftA : A.eval a ≠ 0 ∨ B.eval a ≠ 0)
    (hleftC : C.eval a ≠ 0 ∨ D.eval a ≠ 0)
    (hrightA : A.eval b ≠ 0 ∨ B.eval b ≠ 0)
    (hrightC : C.eval b ≠ 0 ∨ D.eval b ≠ 0) :
    AuxiliaryProductFormula A B C D a b :=
  (auxiliaryProductFormula_swap A B C D a b).mpr
    (auxiliaryProductFormula_of_leftImaginary_zero
      hD hleftC hleftA hrightC hrightA)

/-- Degenerate row where the imaginary coordinate of the complex product is
identically zero.  The two factor indices cancel by cross-product invariance
and numerator oddness, while both raw endpoint corrections are constant. -/
theorem auxiliaryProductFormula_of_productDenominator_zero
    {A B C D : RatPolynomial} {a b : ℚ}
    (hA : A.isZero = false) (hB : B.isZero = false)
    (hC : C.isZero = false) (hD : D.isZero = false)
    (hH : (productDenominator A B C D).isZero = true) :
    AuxiliaryProductFormula A B C D a b := by
  have hHPolynomial :
      (productDenominator A B C D).toPolynomial = 0 :=
    (toPolynomial_eq_zero_iff_isZero _).2 hH
  have hnegC : (-C).isZero = false := by simpa using hC
  have hcross : A.toPolynomial * D.toPolynomial =
      (-C).toPolynomial * B.toPolynomial := by
    simp only [productDenominator, toPolynomial_add, toPolynomial_mul]
      at hHPolynomial
    simp only [toPolynomial_neg]
    linear_combination hHPolynomial
  have hindexCross : cauchyIndex2 (-C) D a b =
      cauchyIndex2 A B a b :=
    cauchyIndex2_eq_of_cross hA hB hnegC hD hcross a b
  have hnegative := cauchyIndex2_neg_numerator C D a b hC hD
  have hsum : cauchyIndex2 A B a b + cauchyIndex2 C D a b = 0 := by
    omega
  have hproductIndex :
      cauchyIndex2 (productNumerator A B C D)
          (productDenominator A B C D) a b = 0 := by
    simp [cauchyIndex2, hH]
  have hcorrection : ∀ x : ℚ,
      auxiliaryEndpointCorrection2 A B C D x = 1 := by
    intro x
    have hHx := eval_eq_zero_of_isZero hH x
    simp only [eval_productDenominator] at hHx
    simp [auxiliaryEndpointCorrection2_eq_signJump,
      hHx, signJump,
      ratSign_of_pos (show (0 : ℚ) < 1 by norm_num)]
  unfold AuxiliaryProductFormula
  rw [hproductIndex, hcorrection a, hcorrection b]
  omega

/-- Degenerate row where the real coordinate of the complex product is
identically zero.  Cauchy inversion supplies the factor-index sum, and the
endpoint correction is its raw pair jump after removing the strictly
positive norm square of the first factor. -/
theorem auxiliaryProductFormula_of_productNumerator_zero
    {A B C D : RatPolynomial} {a b : ℚ}
    (hA : A.isZero = false) (hB : B.isZero = false)
    (hC : C.isZero = false) (hD : D.isZero = false)
    (hE : (productNumerator A B C D).isZero = true)
    (hleftA : A.eval a ≠ 0 ∨ B.eval a ≠ 0)
    (hleftC : C.eval a ≠ 0 ∨ D.eval a ≠ 0)
    (hrightA : A.eval b ≠ 0 ∨ B.eval b ≠ 0)
    (hrightC : C.eval b ≠ 0 ∨ D.eval b ≠ 0) :
    AuxiliaryProductFormula A B C D a b := by
  have hEPolynomial : (productNumerator A B C D).toPolynomial = 0 :=
    (toPolynomial_eq_zero_iff_isZero _).2 hE
  have hcross : A.toPolynomial * C.toPolynomial =
      D.toPolynomial * B.toPolynomial := by
    simp only [productNumerator, toPolynomial_sub, toPolynomial_mul]
      at hEPolynomial
    linear_combination hEPolynomial
  have hindexCross : cauchyIndex2 D C a b =
      cauchyIndex2 A B a b :=
    cauchyIndex2_eq_of_cross hA hB hD hC hcross a b
  have hinversion := cauchyIndex2_inversion C D a b hC hD
  have hpairDifference :=
    pairVariationDifference2_eq_raw_product_jumps
      hC hD hleftC hrightC
  have hproductIndex :
      cauchyIndex2 (productNumerator A B C D)
          (productDenominator A B C D) a b = 0 := by
    simp [cauchyIndex2, hE]
  have hcorrection : ∀ x : ℚ,
      (A.eval x ≠ 0 ∨ B.eval x ≠ 0) →
      auxiliaryEndpointCorrection2 A B C D x =
        signJump 1 (C.eval x * D.eval x) := by
    intro x hfactor
    have hnorm : 0 < A.eval x ^ 2 + B.eval x ^ 2 := by
      rcases hfactor with hAx | hBx
      · nlinarith [sq_pos_of_ne_zero hAx, sq_nonneg (B.eval x)]
      · nlinarith [sq_nonneg (A.eval x), sq_pos_of_ne_zero hBx]
    have hEx := eval_eq_zero_of_isZero hE x
    simp only [eval_productNumerator] at hEx
    have hrelation : A.eval x * C.eval x = B.eval x * D.eval x :=
      sub_eq_zero.mp hEx
    have hfirst : A.eval x * B.eval x * D.eval x ^ 2 =
        A.eval x ^ 2 * C.eval x * D.eval x := by
      calc
        A.eval x * B.eval x * D.eval x ^ 2 =
            A.eval x * D.eval x * (B.eval x * D.eval x) := by ring
        _ = A.eval x * D.eval x * (A.eval x * C.eval x) := by
          rw [hrelation]
        _ = A.eval x ^ 2 * C.eval x * D.eval x := by ring
    have hargument :
        (A.eval x * D.eval x + B.eval x * C.eval x) *
            (B.eval x * D.eval x) =
          (A.eval x ^ 2 + B.eval x ^ 2) *
            (C.eval x * D.eval x) := by
      calc
        (A.eval x * D.eval x + B.eval x * C.eval x) *
              (B.eval x * D.eval x) =
            A.eval x * B.eval x * D.eval x ^ 2 +
              B.eval x ^ 2 * C.eval x * D.eval x := by ring
        _ = A.eval x ^ 2 * C.eval x * D.eval x +
              B.eval x ^ 2 * C.eval x * D.eval x := by rw [hfirst]
        _ = (A.eval x ^ 2 + B.eval x ^ 2) *
              (C.eval x * D.eval x) := by ring
    have hscaled := signJump_mul_mul_of_mul_pos
      (a := (1 : ℚ)) (b := A.eval x ^ 2 + B.eval x ^ 2)
      (x := (1 : ℚ)) (y := C.eval x * D.eval x) (by simpa using hnorm)
    rw [auxiliaryEndpointCorrection2_eq_signJump, hargument]
    simpa only [one_mul] using hscaled
  unfold AuxiliaryProductFormula
  rw [hpairDifference] at hinversion
  rw [hproductIndex, hcorrection a hleftA, hcorrection b hrightA]
  omega

/-- Complete oriented auxiliary product formula under exactly the endpoint
nonvanishing hypotheses.  The finite split covers zero factor coordinates,
zero product coordinates, and finally the recursively partitioned
nondegenerate row. -/
theorem auxiliaryProductFormula_of_endpoint_nonzero_of_ne
    {A B C D : RatPolynomial} {a b : ℚ}
    (hleftA : A.eval a ≠ 0 ∨ B.eval a ≠ 0)
    (hleftC : C.eval a ≠ 0 ∨ D.eval a ≠ 0)
    (hrightA : A.eval b ≠ 0 ∨ B.eval b ≠ 0)
    (hrightC : C.eval b ≠ 0 ∨ D.eval b ≠ 0)
    (hab : a ≠ b) :
    AuxiliaryProductFormula A B C D a b := by
  by_cases hBZero : B.isZero = true
  · exact auxiliaryProductFormula_of_leftImaginary_zero
      hBZero hleftA hleftC hrightA hrightC
  have hB : B.isZero = false := by simpa using hBZero
  by_cases hDZero : D.isZero = true
  · exact auxiliaryProductFormula_of_rightImaginary_zero
      hDZero hleftA hleftC hrightA hrightC
  have hD : D.isZero = false := by simpa using hDZero
  by_cases hAZero : A.isZero = true
  · exact auxiliaryProductFormula_of_leftReal_zero
      hAZero hB hD hleftA hleftC hrightA hrightC
  have hA : A.isZero = false := by simpa using hAZero
  by_cases hCZero : C.isZero = true
  · exact auxiliaryProductFormula_of_rightReal_zero
      hCZero hD hB hleftA hleftC hrightA hrightC
  have hC : C.isZero = false := by simpa using hCZero
  by_cases hHZero : (productDenominator A B C D).isZero = true
  · exact auxiliaryProductFormula_of_productDenominator_zero
      hA hB hC hD hHZero
  have hH : (productDenominator A B C D).isZero = false := by
    simpa using hHZero
  by_cases hEZero : (productNumerator A B C D).isZero = true
  · exact auxiliaryProductFormula_of_productNumerator_zero
      hA hB hC hD hEZero hleftA hleftC hrightA hrightC
  have hE : (productNumerator A B C D).isZero = false := by
    simpa using hEZero
  exact auxiliaryProductFormula_of_nonzero_coordinates_of_ne
    hA hB hC hD hE hH hleftA hleftC hrightA hrightC hab

private def constantOne : RatPolynomial := ⟨[1]⟩
private def variableT : RatPolynomial := ⟨[1, 0]⟩
private def variableTMinusOne : RatPolynomial := ⟨[-1, 1]⟩

/-- The raw-denominator pole convention deliberately repairs the usual
bad-endpoint example `P=1`, `Q=T`, `R=T-1`, `S=T`.  A correction based on
the gcd-reduced value of `(PS+QR)/(QS)` would miss the common zero at the
left endpoint; `endpointFractionSign` records that displayed zero
denominator as a pole and the executable identity succeeds. -/
theorem rawPoleCorrection_badEndpoint_example :
    auxiliaryProductFormulaCheck constantOne variableT
      variableTMinusOne variableT 0 1 = true := by
  native_decide

/-- The exhaustive event-sign search finds the simultaneous pole of
`(1/T)+(1/T)` without naming its parameter value. -/
theorem commonPole_localEventData?_isSome :
    (localEventData? constantOne variableT constantOne variableT
      (-1 / 2) (1 / 2)).isSome = true := by
  native_decide

/-- The combined executable leaf classifier chooses the same simultaneous
pole cell. -/
theorem commonPole_localProductLeaf?_isSome :
    (localProductLeaf? constantOne variableT constantOne variableT
      (-1 / 2) (1 / 2)).isSome = true := by
  native_decide

/-- The recursive partition builder accepts an already classified event cell
at depth zero. -/
theorem commonPole_buildAuxiliaryProductPartition?_isSome :
    (buildAuxiliaryProductPartition? constantOne variableT
      constantOne variableT 0 (-1 / 2) (1 / 2)).isSome = true := by
  native_decide

/-- Regression covering the simultaneous-pole case
`(1/T) + (1/T)`: the product coordinates are `1-T²` and `2T`. -/
theorem commonPole_auxiliaryProductFormula_check :
    auxiliaryProductFormulaCheck
      constantOne variableT constantOne variableT (-1) 1 = true := by
  native_decide

end FTA.CauchyProduct
