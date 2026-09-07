import FTA.Winding
import FTA.SafeCandidates
import FTA.SturmTransducer

/-!
# Algebraic prerequisites for the finite Cauchy-index product formula

This module states the doubled auxiliary product formula for four rational
coordinate polynomials.  It proves the paper's pole-sign convention,
same-sign invariance of signed Euclidean chains, rational-function
extensionality and product transfer after executable gcd reduction,
exhaustive one-sided and two-sided finite
event tables, exhaustive six-sign leaf classification, and a safe-cut
fuel-recursive simultaneous-event partition builder.  Every returned
partition is sound, and any positive local classifier width is converted by
rational ceiling arithmetic into a proved successful depth.  The neutral
branch and all interior event leaves now have positive coefficient-computed
widths for their three gcd-reduced Cauchy chains.  Each individual event
chain constructs exact formal center signs, lifts them constructively to the
original coprime coordinates, and the compatible three-record assembly is
accepted by the exhaustive product leaf.  A coefficient-only complex-norm
estimate also resolves the possibly nonconstant common gcd of the product
coordinates and lifts their reduced-chain event record.  Formal centers may
be re-centered at either exact rational boundary, where their event indices
reduce to the paper's one-sided pole terms.  Positive endpoint Lipschitz
widths make both genuine boundary leaf branches succeed.  A guard-aware
recursive invariant lifts the interior and boundary cases through the actual
safe-cut builder at an explicit rational ceiling depth, producing a total
auxiliary product-partition program with no universal success assumption.
-/

namespace FTA.CauchyProduct

open FTA.ComputablePolynomial
open ComputablePolynomial.DensePolynomial
open FTA.RationalPolynomialBounds
open FTA.Sturm

abbrev RatPolynomial := DensePolynomial ℚ

/-- Sign of a rational function at one rational endpoint.  A zero denominator
uses the pole convention `sign(∞) = 0`. -/
def endpointFractionSign (N D : RatPolynomial) (x : ℚ) : ℤ :=
  if D.eval x = 0 then 0 else ratSign (N.eval x / D.eval x)

/-- Doubled two-entry variation `Var(1,N/D)` at one endpoint. -/
def endpointFractionVariation2 (N D : RatPolynomial) (x : ℚ) : ℕ :=
  (1 - endpointFractionSign N D x).natAbs

/-- With the pole convention, the sign of `N/D` is computed without division
as the sign of `N*D`. -/
theorem endpointFractionSign_eq_ratSign_mul
    (N D : RatPolynomial) (x : ℚ) :
    endpointFractionSign N D x = ratSign (N.eval x * D.eval x) := by
  by_cases hD : D.eval x = 0
  · simp [endpointFractionSign, hD]
  · have hDsq : 0 < D.eval x ^ 2 := sq_pos_of_ne_zero hD
    have hquotient :
        N.eval x / D.eval x =
          (N.eval x * D.eval x) / (D.eval x ^ 2) := by
      field_simp
    rw [endpointFractionSign, if_neg hD, hquotient]
    rcases lt_trichotomy (N.eval x * D.eval x) 0 with hneg | hzero | hpos
    · rw [ratSign_of_neg hneg,
        ratSign_of_neg (div_neg_of_neg_of_pos hneg hDsq)]
    · rw [hzero]
      simp
    · rw [ratSign_of_pos hpos,
        ratSign_of_pos (div_pos hpos hDsq)]

/-- The executable correction is exactly the doubled two-entry sign jump. -/
theorem endpointFractionVariation2_eq_signJump
    (N D : RatPolynomial) (x : ℚ) :
    endpointFractionVariation2 N D x =
      signJump 1 (N.eval x * D.eval x) := by
  rw [endpointFractionVariation2, endpointFractionSign_eq_ratSign_mul]
  simp [signJump, ratSign_of_pos (show (0 : ℚ) < 1 by norm_num)]

/-- Real coordinate `AC-BD` of the product of `A+iB` and `C+iD`. -/
def productNumerator
    (A B C D : RatPolynomial) : RatPolynomial :=
  A * C - B * D

/-- Imaginary coordinate `AD+BC` of the same product. -/
def productDenominator
    (A B C D : RatPolynomial) : RatPolynomial :=
  A * D + B * C

@[simp] theorem eval_productNumerator
    (A B C D : RatPolynomial) (x : ℚ) :
    (productNumerator A B C D).eval x =
      A.eval x * C.eval x - B.eval x * D.eval x := by
  simp [productNumerator]

@[simp] theorem eval_productDenominator
    (A B C D : RatPolynomial) (x : ℚ) :
    (productDenominator A B C D).eval x =
      A.eval x * D.eval x + B.eval x * C.eval x := by
  simp [productDenominator]

/-- Exact complex multiplication over the rationals has no zero divisors,
expressed only through the two coordinate formulas used by the finite sign
tables. -/
theorem complexProductCoordinates_ne_zero
    {A B C D : ℚ}
    (hleft : A ≠ 0 ∨ B ≠ 0) (hright : C ≠ 0 ∨ D ≠ 0) :
    A * C - B * D ≠ 0 ∨ A * D + B * C ≠ 0 := by
  by_contra hproduct
  rw [not_or, not_ne_iff, not_ne_iff] at hproduct
  have hleftNorm : 0 < A ^ 2 + B ^ 2 := by
    rcases hleft with hA | hB
    · nlinarith [sq_pos_of_ne_zero hA]
    · nlinarith [sq_pos_of_ne_zero hB]
  have hrightNorm : 0 < C ^ 2 + D ^ 2 := by
    rcases hright with hC | hD
    · nlinarith [sq_pos_of_ne_zero hC]
    · nlinarith [sq_pos_of_ne_zero hD]
  have hnorm :
      (A * C - B * D) ^ 2 + (A * D + B * C) ^ 2 =
        (A ^ 2 + B ^ 2) * (C ^ 2 + D ^ 2) := by
    ring
  rw [hproduct.1, hproduct.2] at hnorm
  nlinarith [mul_pos hleftNorm hrightNorm]

/-- A displayed dense Bézout identity rules out simultaneous vanishing at
every rational point. -/
theorem coprimePair_eval_ne_zero
    {P Q : RatPolynomial}
    (certificate : FTA.DenseSquarefree.CoprimeCertificate P Q) (x : ℚ) :
    P.eval x ≠ 0 ∨ Q.eval x ≠ 0 := by
  by_contra hzero
  rw [not_or, not_ne_iff, not_ne_iff] at hzero
  have hone := certificate.identity x
  rw [hzero.1, hzero.2] at hone
  norm_num at hone

/-- A product of two nonzero executable rational polynomials remains
nonzero. -/
theorem isZero_mul_eq_false {p q : RatPolynomial}
    (hp : p.isZero = false) (hq : q.isZero = false) :
    (p * q).isZero = false :=
  FTA.ComputablePolynomial.DensePolynomial.isZero_mul_eq_false hp hq

theorem isZero_false_of_toPolynomial_ne_zero {p : RatPolynomial}
    (hp : p.toPolynomial ≠ 0) : p.isZero = false := by
  cases hzero : p.isZero with
  | false => rfl
  | true => exact (hp ((toPolynomial_eq_zero_iff_isZero p).2 hzero)).elim

theorem isZero_false_of_eval_ne_zero {p : RatPolynomial} {x : ℚ}
    (hp : p.eval x ≠ 0) : p.isZero = false := by
  cases hzero : p.isZero with
  | false => rfl
  | true => exact (hp (eval_eq_zero_of_isZero hzero x)).elim

/-- Doubled endpoint correction for `(AD+BC)/(BD)`. -/
def auxiliaryEndpointCorrection2
    (A B C D : RatPolynomial) (x : ℚ) : ℕ :=
  endpointFractionVariation2 (productDenominator A B C D) (B * D) x

/-- Expanded finite sign-jump form of the auxiliary endpoint correction. -/
theorem auxiliaryEndpointCorrection2_eq_signJump
    (A B C D : RatPolynomial) (x : ℚ) :
    auxiliaryEndpointCorrection2 A B C D x =
      signJump 1
        ((A.eval x * D.eval x + B.eval x * C.eval x) *
          (B.eval x * D.eval x)) := by
  rw [auxiliaryEndpointCorrection2,
    endpointFractionVariation2_eq_signJump]
  simp only [eval_productDenominator, eval_mul]

/-- The exact doubled auxiliary product formula on an oriented interval. -/
def AuxiliaryProductFormula
    (A B C D : RatPolynomial) (a b : ℚ) : Prop :=
  cauchyIndex2 (productNumerator A B C D)
      (productDenominator A B C D) a b =
    cauchyIndex2 A B a b + cauchyIndex2 C D a b -
      (auxiliaryEndpointCorrection2 A B C D a : ℤ) +
      auxiliaryEndpointCorrection2 A B C D b

/-- Finite Boolean certificate for one auxiliary product-formula instance. -/
def auxiliaryProductFormulaCheck
    (A B C D : RatPolynomial) (a b : ℚ) : Bool :=
  decide
    (cauchyIndex2 (productNumerator A B C D)
        (productDenominator A B C D) a b =
      cauchyIndex2 A B a b + cauchyIndex2 C D a b -
        (auxiliaryEndpointCorrection2 A B C D a : ℤ) +
        auxiliaryEndpointCorrection2 A B C D b)

/-- Soundness of the finite auxiliary product certificate. -/
theorem auxiliaryProductFormula_of_check
    (A B C D : RatPolynomial) (a b : ℚ)
    (hcheck : auxiliaryProductFormulaCheck A B C D a b = true) :
    AuxiliaryProductFormula A B C D a b := by
  simpa [auxiliaryProductFormulaCheck, AuxiliaryProductFormula] using hcheck

/-- Auxiliary product formulas compose under interval subdivision; the middle
endpoint correction cancels exactly. -/
theorem AuxiliaryProductFormula.add
    {A B C D : RatPolynomial} {a b c : ℚ}
    (hab : AuxiliaryProductFormula A B C D a b)
    (hbc : AuxiliaryProductFormula A B C D b c) :
    AuxiliaryProductFormula A B C D a c := by
  rw [AuxiliaryProductFormula] at hab hbc ⊢
  have hproduct := cauchyIndex2_add
    (productNumerator A B C D) (productDenominator A B C D) a b c
  have hleft := cauchyIndex2_add A B a b c
  have hright := cauchyIndex2_add C D a b c
  omega

/-- Reversing an interval reverses the auxiliary product formula. -/
theorem AuxiliaryProductFormula.reverse
    {A B C D : RatPolynomial} {a b : ℚ}
    (hab : AuxiliaryProductFormula A B C D a b) :
    AuxiliaryProductFormula A B C D b a := by
  rw [AuxiliaryProductFormula] at hab ⊢
  rw [cauchyIndex2_reverse
      (productNumerator A B C D) (productDenominator A B C D) a b,
    cauchyIndex2_reverse A B a b,
    cauchyIndex2_reverse C D a b]
  omega

/-- The auxiliary product formula is trivial on a reflexive interval. -/
theorem auxiliaryProductFormula_refl
    (A B C D : RatPolynomial) (a : ℚ) :
    AuxiliaryProductFormula A B C D a a := by
  simp [AuxiliaryProductFormula]

/-! ## Finite local product sign table -/

/-- The three exact signs used by every endpoint table. -/
inductive FiniteSign where
  | negative
  | zero
  | positive
deriving DecidableEq, Repr

/-- Explicit finite enumeration.  Writing the three cases directly avoids
the choice-dependent `List.range` proof generated by `deriving Fintype`. -/
instance : Fintype FiniteSign where
  elems := {.negative, .zero, .positive}
  complete sign := by cases sign <;> simp

namespace FiniteSign

/-- Integer realization in `{-1,0,1}`. -/
def value : FiniteSign → ℤ
  | negative => -1
  | zero => 0
  | positive => 1

/-- Exact sign of a rational. -/
def ofRat (x : ℚ) : FiniteSign :=
  if x < 0 then negative else if x = 0 then zero else positive

/-- Finite sign multiplication. -/
def mul : FiniteSign → FiniteSign → FiniteSign
  | zero, _ => zero
  | _, zero => zero
  | positive, y => y
  | x, positive => x
  | negative, negative => positive

/-- Finite sign negation. -/
def neg : FiniteSign → FiniteSign
  | negative => positive
  | zero => zero
  | positive => negative

/-- Doubled jump between two finite signs. -/
def jump (x y : FiniteSign) : ℕ := (x.value - y.value).natAbs

theorem value_injective : Function.Injective value := by
  intro x y h
  cases x <;> cases y <;> simp [value] at h ⊢

@[simp] theorem value_ofRat (x : ℚ) : value (ofRat x) = ratSign x := by
  by_cases hx : x < 0
  · simp [ofRat, value, ratSign, hx]
  · by_cases hx0 : x = 0
    · simp [ofRat, value, ratSign, hx0]
    · simp [ofRat, value, ratSign, hx, hx0]

@[simp] theorem ofRat_zero : ofRat 0 = zero := rfl

theorem ofRat_eq_zero_iff {x : ℚ} : ofRat x = zero ↔ x = 0 := by
  constructor
  · intro h
    have hv := congrArg value h
    rw [value_ofRat] at hv
    change ratSign x = 0 at hv
    exact ratSign_eq_zero_iff.mp hv
  · rintro rfl
    rfl

theorem ofRat_of_neg {x : ℚ} (hx : x < 0) : ofRat x = negative := by
  simp [ofRat, hx]

theorem ofRat_of_pos {x : ℚ} (hx : 0 < x) : ofRat x = positive := by
  simp [ofRat, hx.ne', not_lt.mpr hx.le]

@[simp] theorem value_mul (x y : FiniteSign) :
    value (mul x y) = value x * value y := by
  cases x <;> cases y <;> decide

@[simp] theorem value_neg (x : FiniteSign) : value (neg x) = -value x := by
  cases x <;> decide

@[simp] theorem ofRat_mul (x y : ℚ) :
    ofRat (x * y) = mul (ofRat x) (ofRat y) := by
  apply value_injective
  simp [ratSign_mul]

@[simp] theorem ofRat_neg (x : ℚ) : ofRat (-x) = neg (ofRat x) := by
  apply value_injective
  simp [ratSign_neg]

@[simp] theorem jump_ofRat (x y : ℚ) :
    jump (ofRat x) (ofRat y) = signJump x y := by
  simp [jump, signJump]

/-- For a nonzero formal pair, its two-entry jump is the jump from the
positive axis to the formal product. -/
theorem jump_eq_positive_mul
    (x y : FiniteSign) (hnonzero : x ≠ zero ∨ y ≠ zero) :
    jump x y = jump positive (mul x y) := by
  decide +revert

/-- Sign-level information forced by `z = x+y`.  Opposite strict signs allow
all three outcomes; every other case fixes the result. -/
def SumCompatible (x y z : FiniteSign) : Prop :=
  if x = zero then z = y
  else if y = zero then z = x
  else if x = y then z = x
  else True

instance (x y z : FiniteSign) : Decidable (SumCompatible x y z) := by
  unfold SumCompatible
  infer_instance

theorem sumCompatible_ofRat (x y : ℚ) :
    SumCompatible (ofRat x) (ofRat y) (ofRat (x + y)) := by
  rcases lt_trichotomy x 0 with hx | rfl | hx <;>
    rcases lt_trichotomy y 0 with hy | rfl | hy
  · have hxy : x + y < 0 := add_neg hx hy
    rw [ofRat_of_neg hx, ofRat_of_neg hy, ofRat_of_neg hxy]
    simp [SumCompatible]
  · simp [add_zero, SumCompatible, ofRat_of_neg hx]
  · rw [ofRat_of_neg hx, ofRat_of_pos hy]
    simp [SumCompatible]
  · simp [zero_add, SumCompatible, ofRat_of_neg hy]
  · simp [SumCompatible]
  · simp [zero_add, SumCompatible, ofRat_of_pos hy]
  · rw [ofRat_of_pos hx, ofRat_of_neg hy]
    simp [SumCompatible]
  · simp [add_zero, SumCompatible, ofRat_of_pos hx]
  · have hxy : 0 < x + y := add_pos hx hy
    rw [ofRat_of_pos hx, ofRat_of_pos hy, ofRat_of_pos hxy]
    simp [SumCompatible]

/-- A nonzero sign remains unchanged across a locally stable cell. -/
def Stable (atEndpoint nearby : FiniteSign) : Prop :=
  atEndpoint = zero ∨ atEndpoint = nearby

instance (atEndpoint nearby : FiniteSign) :
    Decidable (Stable atEndpoint nearby) := by
  unfold Stable
  infer_instance

/-- Allowed signs for `(AC-BD)+i(AD+BC)`. -/
def ComplexProductCompatible
    (A B C D E H : FiniteSign) : Prop :=
  SumCompatible (mul A C) (neg (mul B D)) E ∧
    SumCompatible (mul A D) (mul B C) H

instance (A B C D E H : FiniteSign) :
    Decidable (ComplexProductCompatible A B C D E H) := by
  unfold ComplexProductCompatible
  infer_instance

/-- Canonical conservative sign of a formal sum.  Opposite nonzero signs
leave the result deliberately unknown (`zero`); every determined case keeps
the forced sign. -/
def sumChoice (x y : FiniteSign) : FiniteSign :=
  if x = zero then y
  else if y = zero then x
  else if x = y then x
  else zero

theorem sumChoice_compatible (x y : FiniteSign) :
    SumCompatible x y (sumChoice x y) := by
  decide +revert

/-- Conservative formal coordinates of a complex product. -/
def productRealChoice (A B C D : FiniteSign) : FiniteSign :=
  sumChoice (mul A C) (neg (mul B D))

def productImagChoice (A B C D : FiniteSign) : FiniteSign :=
  sumChoice (mul A D) (mul B C)

theorem productChoices_compatible (A B C D : FiniteSign) :
    ComplexProductCompatible A B C D
      (productRealChoice A B C D) (productImagChoice A B C D) := by
  decide +revert

/-- Two nonzero formal complex factors always leave at least one determined
nonzero product coordinate. -/
theorem productChoices_nonzero (A B C D : FiniteSign)
    (hleft : A ≠ zero ∨ B ≠ zero)
    (hright : C ≠ zero ∨ D ≠ zero) :
    productRealChoice A B C D ≠ zero ∨
      productImagChoice A B C D ≠ zero := by
  decide +revert

/-- The complete hypotheses of one right-sided local endpoint cell. -/
def LocalProductAdmissible
    (A₀ B₀ C₀ D₀ E₀ H₀ A₁ B₁ C₁ D₁ E₁ H₁ : FiniteSign) : Prop :=
  (A₀ ≠ zero ∨ B₀ ≠ zero) ∧
  (C₀ ≠ zero ∨ D₀ ≠ zero) ∧
  B₁ ≠ zero ∧ D₁ ≠ zero ∧ H₁ ≠ zero ∧
  Stable A₀ A₁ ∧ Stable B₀ B₁ ∧
  Stable C₀ C₁ ∧ Stable D₀ D₁ ∧
  Stable E₀ E₁ ∧ Stable H₀ H₁ ∧
  ComplexProductCompatible A₀ B₀ C₀ D₀ E₀ H₀ ∧
  ComplexProductCompatible A₁ B₁ C₁ D₁ E₁ H₁

instance (A₀ B₀ C₀ D₀ E₀ H₀ A₁ B₁ C₁ D₁ E₁ H₁ : FiniteSign) :
    Decidable (LocalProductAdmissible
      A₀ B₀ C₀ D₀ E₀ H₀ A₁ B₁ C₁ D₁ E₁ H₁) := by
  unfold LocalProductAdmissible
  infer_instance

/-- Doubled local index contributed by a pole at the left endpoint. -/
def leftEndpointIndex2
    (_P₀ Q₀ P₁ Q₁ : FiniteSign) : ℤ :=
  if Q₀ = zero then value (mul P₁ Q₁) else 0

/-- Doubled correction `Var(1,H/(BD))` from three finite signs. -/
def productCorrection2 (H B D : FiniteSign) : ℕ :=
  jump positive (mul H (mul B D))

/-- The local equality checked by the paper's endpoint sign table. -/
def LocalProductIdentity
    (A₀ B₀ C₀ D₀ E₀ H₀ A₁ B₁ C₁ D₁ E₁ H₁ : FiniteSign) : Prop :=
  leftEndpointIndex2 E₀ H₀ E₁ H₁ =
    leftEndpointIndex2 A₀ B₀ A₁ B₁ +
      leftEndpointIndex2 C₀ D₀ C₁ D₁ -
      (productCorrection2 H₀ B₀ D₀ : ℤ) +
      productCorrection2 H₁ B₁ D₁

instance (A₀ B₀ C₀ D₀ E₀ H₀ A₁ B₁ C₁ D₁ E₁ H₁ : FiniteSign) :
    Decidable (LocalProductIdentity
      A₀ B₀ C₀ D₀ E₀ H₀ A₁ B₁ C₁ D₁ E₁ H₁) := by
  unfold LocalProductIdentity
  infer_instance

theorem mul_ne_zero {x y : FiniteSign}
    (hx : x ≠ zero) (hy : y ≠ zero) : mul x y ≠ zero := by
  decide +revert

private theorem eq_of_stable_of_ne_zero {x y : FiniteSign}
    (hstable : Stable x y) (hx : x ≠ zero) : x = y :=
  hstable.resolve_left hx

private theorem compatible_both_denominators_zero
    (A C E H : FiniteSign)
    (h : ComplexProductCompatible A zero C zero E H) :
    E = mul A C ∧ H = zero := by
  decide +revert

private theorem compatible_left_denominator_zero
    (A C D E H : FiniteSign)
    (h : ComplexProductCompatible A zero C D E H) :
    H = mul A D := by
  decide +revert

private theorem compatible_right_denominator_zero
    (A B C E H : FiniteSign)
    (h : ComplexProductCompatible A B C zero E H) :
    H = mul B C := by
  decide +revert

private theorem real_nonzero_of_imag_zero
    (A B C D E : FiniteSign)
    (hB : B ≠ zero) (hD : D ≠ zero)
    (h : ComplexProductCompatible A B C D E zero) : E ≠ zero := by
  decide +revert

private theorem correction_identity_left_zero
    (A D B : FiniteSign)
    (hA : A ≠ zero) (hD : D ≠ zero) (hB : B ≠ zero) :
    (0 : ℤ) = value (mul A B) -
      (productCorrection2 (mul A D) zero D : ℤ) +
      productCorrection2 (mul A D) B D := by
  decide +revert

private theorem correction_identity_right_zero
    (B C D : FiniteSign)
    (hB : B ≠ zero) (hC : C ≠ zero) (hD : D ≠ zero) :
    (0 : ℤ) = value (mul C D) -
      (productCorrection2 (mul B C) B zero : ℤ) +
      productCorrection2 (mul B C) B D := by
  decide +revert

private theorem correction_identity_both_zero
    (A C B D H : FiniteSign)
    (hA : A ≠ zero) (hC : C ≠ zero)
    (hB : B ≠ zero) (hD : D ≠ zero) (hH : H ≠ zero)
    (hprod : ComplexProductCompatible A B C D (mul A C) H) :
    value (mul (mul A C) H) =
      value (mul A B) + value (mul C D) -
        (productCorrection2 zero zero zero : ℤ) +
        productCorrection2 H B D := by
  decide +revert

private theorem correction_identity_imag_zero
    (A B C D E H : FiniteSign)
    (hB : B ≠ zero) (hD : D ≠ zero) (hH : H ≠ zero)
    (hprod : ComplexProductCompatible A B C D E zero) :
    value (mul E H) =
      -(productCorrection2 zero B D : ℤ) +
        productCorrection2 H B D := by
  decide +revert

/-- Exhaustive local product theorem.  The proof first splits on the three
endpoint denominator signs.  Each remaining sign identity has at most six
finite inputs, so ordinary kernel reduction checks it quickly without a
native-computation axiom or a special resource limit.  As before,
`ComplexProductCompatible` allows every sign when two summands have opposite
signs, so no magnitude comparison is hidden in these finite checks. -/
theorem localProductTable :
    ∀ A₀ B₀ C₀ D₀ E₀ H₀ A₁ B₁ C₁ D₁ E₁ H₁ : FiniteSign,
      LocalProductAdmissible
          A₀ B₀ C₀ D₀ E₀ H₀ A₁ B₁ C₁ D₁ E₁ H₁ →
        LocalProductIdentity
          A₀ B₀ C₀ D₀ E₀ H₀ A₁ B₁ C₁ D₁ E₁ H₁ := by
  intro A₀ B₀ C₀ D₀ E₀ H₀ A₁ B₁ C₁ D₁ E₁ H₁ h
  rcases h with ⟨hAB₀, hCD₀, hB₁, hD₁, hH₁,
    hA, hB, hC, hD, hE, hH, hprod₀, hprod₁⟩
  by_cases hB₀ : B₀ = zero
  · subst B₀
    have hA₀ : A₀ ≠ zero := by simpa using hAB₀
    have hAA₁ := eq_of_stable_of_ne_zero hA hA₀
    subst A₁
    by_cases hD₀ : D₀ = zero
    · subst D₀
      have hC₀ : C₀ ≠ zero := by simpa using hCD₀
      have hCC₁ := eq_of_stable_of_ne_zero hC hC₀
      subst C₁
      obtain ⟨hE₀, rfl⟩ :=
        compatible_both_denominators_zero A₀ C₀ E₀ H₀ hprod₀
      rw [hE₀] at hE ⊢
      have hmulAC : mul A₀ C₀ ≠ zero := mul_ne_zero hA₀ hC₀
      have hEE₁ := eq_of_stable_of_ne_zero hE hmulAC
      subst E₁
      unfold LocalProductIdentity leftEndpointIndex2
      simpa using correction_identity_both_zero
        A₀ C₀ B₁ D₁ H₁ hA₀ hC₀ hB₁ hD₁ hH₁ hprod₁
    · have hDD₁ := eq_of_stable_of_ne_zero hD hD₀
      subst D₁
      have hH₀ :=
        compatible_left_denominator_zero A₀ C₀ D₀ E₀ H₀ hprod₀
      have hmulAD : mul A₀ D₀ ≠ zero := mul_ne_zero hA₀ hD₀
      rw [hH₀] at hH ⊢
      have hHH₁ := eq_of_stable_of_ne_zero hH hmulAD
      subst H₁
      unfold LocalProductIdentity leftEndpointIndex2
      simp only [if_neg hD₀, if_neg hmulAD, add_zero]
      exact correction_identity_left_zero A₀ D₀ B₁ hA₀ hD₀ hB₁
  · have hBB₁ := eq_of_stable_of_ne_zero hB hB₀
    subst B₁
    by_cases hD₀ : D₀ = zero
    · subst D₀
      have hC₀ : C₀ ≠ zero := by simpa using hCD₀
      have hCC₁ := eq_of_stable_of_ne_zero hC hC₀
      subst C₁
      have hH₀ :=
        compatible_right_denominator_zero A₀ B₀ C₀ E₀ H₀ hprod₀
      have hmulBC : mul B₀ C₀ ≠ zero := mul_ne_zero hB₀ hC₀
      rw [hH₀] at hH ⊢
      have hHH₁ := eq_of_stable_of_ne_zero hH hmulBC
      subst H₁
      unfold LocalProductIdentity leftEndpointIndex2
      simp only [if_neg hB₀, if_neg hmulBC, zero_add]
      exact correction_identity_right_zero B₀ C₀ D₁ hB₀ hC₀ hD₁
    · have hDD₁ := eq_of_stable_of_ne_zero hD hD₀
      subst D₁
      by_cases hH₀ : H₀ = zero
      · subst H₀
        have hE₀ :=
          real_nonzero_of_imag_zero A₀ B₀ C₀ D₀ E₀ hB₀ hD₀ hprod₀
        have hEE₁ := eq_of_stable_of_ne_zero hE hE₀
        subst E₁
        unfold LocalProductIdentity leftEndpointIndex2
        simp only [if_neg hB₀, if_neg hD₀, zero_add, zero_sub]
        exact correction_identity_imag_zero
          A₀ B₀ C₀ D₀ E₀ H₁ hB₀ hD₀ hH₁ hprod₀
      · have hHH₁ := eq_of_stable_of_ne_zero hH hH₀
        subst H₁
        simp [LocalProductIdentity, leftEndpointIndex2,
          hB₀, hD₀, hH₀]

/-- Net doubled index contributed by one isolated event.  The two
`leftEndpointIndex2` terms are the right and left half-contributions from the
same formal event sign; subtracting them removes any need to name the event
by an exact rational parameter. -/
def eventIndex2
    (Pₑ Qₑ Pₗ Qₗ Pᵣ Qᵣ : FiniteSign) : ℤ :=
  leftEndpointIndex2 Pₑ Qₑ Pᵣ Qᵣ -
    leftEndpointIndex2 Pₑ Qₑ Pₗ Qₗ

/-- Re-centering a formal event at its displayed left endpoint turns the
two-sided event index into exactly the one-sided left-endpoint contribution.
The subtracted self-contribution vanishes even when the denominator sign is
zero, because then the numerator-denominator product is zero. -/
theorem eventIndex2_self_left
    (P Q Pᵣ Qᵣ : FiniteSign) :
    eventIndex2 P Q P Q Pᵣ Qᵣ =
      leftEndpointIndex2 P Q Pᵣ Qᵣ := by
  decide +revert

/-- With the formal center fixed to the displayed right endpoint, reversing
the event orientation yields its one-sided contribution at that endpoint. -/
theorem neg_eventIndex2_self_right
    (P Q Pₗ Qₗ : FiniteSign) :
    -eventIndex2 P Q Pₗ Qₗ P Q =
      leftEndpointIndex2 P Q Pₗ Qₗ := by
  decide +revert

/-- A nonzero formal pair that is stable against both displayed endpoints. -/
def EventCenterAdmissible
    (P Q Pₗ Qₗ Pᵣ Qᵣ : FiniteSign) : Prop :=
  (P ≠ zero ∨ Q ≠ zero) ∧
    Stable P Pₗ ∧ Stable Q Qₗ ∧ Stable P Pᵣ ∧ Stable Q Qᵣ

instance (P Q Pₗ Qₗ Pᵣ Qᵣ : FiniteSign) :
    Decidable (EventCenterAdmissible P Q Pₗ Qₗ Pᵣ Qᵣ) := by
  unfold EventCenterAdmissible
  infer_instance

/-- The formal event index is independent of the chosen nonzero stable
center representative.  This permits coordinated re-centering of three
Cauchy records without changing any computed chain index. -/
theorem eventIndex2_eq_of_stable
    : ∀ P Q P' Q' Pₗ Qₗ Pᵣ Qᵣ : FiniteSign,
      EventCenterAdmissible P Q Pₗ Qₗ Pᵣ Qᵣ →
      EventCenterAdmissible P' Q' Pₗ Qₗ Pᵣ Qᵣ →
      eventIndex2 P Q Pₗ Qₗ Pᵣ Qᵣ =
        eventIndex2 P' Q' Pₗ Qₗ Pᵣ Qᵣ := by
  decide

/-- When the formal denominator vanishes and the numerator has one fixed
nonzero sign, the formal event index is exactly the change of the first
two-entry sign jump. -/
theorem eventIndex2_of_stableNumerator
    (P Qₗ Qᵣ : FiniteSign) (hP : P ≠ zero) :
    eventIndex2 P zero P Qₗ P Qᵣ =
      (jump Qₗ P : ℤ) - jump Qᵣ P := by
  decide +revert

/-- Multiplying both signs by the same formal scalar preserves stability. -/
theorem stable_mul_left (k x y : FiniteSign) (hxy : Stable x y) :
    Stable (mul k x) (mul k y) := by
  rcases hxy with rfl | rfl
  · exact Or.inl (by cases k <;> rfl)
  · exact Or.inr rfl

/-- Independent common scales on the two complex factors scale both product
coordinates by their formal product and preserve compatibility. -/
theorem complexProductCompatible_mul_scales
    (k l A B C D E H : FiniteSign)
    (h : ComplexProductCompatible A B C D E H) :
    ComplexProductCompatible
      (mul k A) (mul k B) (mul l C) (mul l D)
      (mul (mul k l) E) (mul (mul k l) H) := by
  decide +revert

theorem complexProductCompatible_of_mul_scales
    (k l A B C D E H : FiniteSign) (hk : k ≠ zero) (hl : l ≠ zero)
    (h : ComplexProductCompatible
      (mul k A) (mul k B) (mul l C) (mul l D)
      (mul (mul k l) E) (mul (mul k l) H)) :
    ComplexProductCompatible A B C D E H := by
  decide +revert

/-- A common nonzero formal scale cancels from a complete event index. -/
theorem eventIndex2_mul_left (k Pₑ Qₑ Pₗ Qₗ Pᵣ Qᵣ : FiniteSign)
    (hk : k ≠ zero) :
    eventIndex2 (mul k Pₑ) (mul k Qₑ)
        (mul k Pₗ) (mul k Qₗ) (mul k Pᵣ) (mul k Qᵣ) =
      eventIndex2 Pₑ Qₑ Pₗ Qₗ Pᵣ Qᵣ := by
  decide +revert

/-- The two-sided local identity around one isolated formal event. -/
def LocalEventProductIdentity
    (Aₑ Bₑ Cₑ Dₑ Eₑ Hₑ
      Aₗ Bₗ Cₗ Dₗ Eₗ Hₗ
      Aᵣ Bᵣ Cᵣ Dᵣ Eᵣ Hᵣ : FiniteSign) : Prop :=
  eventIndex2 Eₑ Hₑ Eₗ Hₗ Eᵣ Hᵣ =
    eventIndex2 Aₑ Bₑ Aₗ Bₗ Aᵣ Bᵣ +
      eventIndex2 Cₑ Dₑ Cₗ Dₗ Cᵣ Dᵣ -
      (productCorrection2 Hₗ Bₗ Dₗ : ℤ) +
      productCorrection2 Hᵣ Bᵣ Dᵣ

/-- The exhaustive one-sided table composes on the two sides of the same
formal event.  The correction at the unrepresented event cancels, leaving
only the two rational cell endpoints. -/
theorem localProductEventTable
    (Aₑ Bₑ Cₑ Dₑ Eₑ Hₑ
      Aₗ Bₗ Cₗ Dₗ Eₗ Hₗ
      Aᵣ Bᵣ Cᵣ Dᵣ Eᵣ Hᵣ : FiniteSign)
    (hleft : LocalProductAdmissible
      Aₑ Bₑ Cₑ Dₑ Eₑ Hₑ Aₗ Bₗ Cₗ Dₗ Eₗ Hₗ)
    (hright : LocalProductAdmissible
      Aₑ Bₑ Cₑ Dₑ Eₑ Hₑ Aᵣ Bᵣ Cᵣ Dᵣ Eᵣ Hᵣ) :
    LocalEventProductIdentity
      Aₑ Bₑ Cₑ Dₑ Eₑ Hₑ
      Aₗ Bₗ Cₗ Dₗ Eₗ Hₗ
      Aᵣ Bᵣ Cᵣ Dᵣ Eᵣ Hᵣ := by
  have hleftIdentity := localProductTable
    Aₑ Bₑ Cₑ Dₑ Eₑ Hₑ Aₗ Bₗ Cₗ Dₗ Eₗ Hₗ hleft
  have hrightIdentity := localProductTable
    Aₑ Bₑ Cₑ Dₑ Eₑ Hₑ Aᵣ Bᵣ Cᵣ Dᵣ Eᵣ Hᵣ hright
  unfold LocalProductIdentity at hleftIdentity hrightIdentity
  unfold LocalEventProductIdentity eventIndex2
  omega

end FiniteSign

/-- Exact rational local pole contribution matching `FiniteSign`'s table. -/
def leftEndpointIndex2 (_P₀ Q₀ P₁ Q₁ : ℚ) : ℤ :=
  if Q₀ = 0 then ratSign (P₁ * Q₁) else 0

/-- The finite-sign local index is exactly the rational local index. -/
theorem finiteSign_leftEndpointIndex2_ofRat
    (P₀ Q₀ P₁ Q₁ : ℚ) :
    FiniteSign.leftEndpointIndex2
        (FiniteSign.ofRat P₀) (FiniteSign.ofRat Q₀)
        (FiniteSign.ofRat P₁) (FiniteSign.ofRat Q₁) =
      leftEndpointIndex2 P₀ Q₀ P₁ Q₁ := by
  by_cases hQ : Q₀ = 0
  · subst Q₀
    simp [FiniteSign.leftEndpointIndex2, leftEndpointIndex2,
      FiniteSign.value_mul, ← ratSign_mul]
  · have hsign : FiniteSign.ofRat Q₀ ≠ FiniteSign.zero := by
      simpa [FiniteSign.ofRat_eq_zero_iff] using hQ
    simp [FiniteSign.leftEndpointIndex2, leftEndpointIndex2, hQ, hsign]

/-- The finite-sign correction is exactly the rational doubled sign jump. -/
theorem finiteSign_productCorrection2_ofRat
    (H B D : ℚ) :
    FiniteSign.productCorrection2
        (FiniteSign.ofRat H) (FiniteSign.ofRat B) (FiniteSign.ofRat D) =
      signJump 1 (H * (B * D)) := by
  unfold FiniteSign.productCorrection2
  change FiniteSign.jump (FiniteSign.ofRat 1)
      (FiniteSign.mul (FiniteSign.ofRat H)
        (FiniteSign.mul (FiniteSign.ofRat B) (FiniteSign.ofRat D))) = _
  rw [← FiniteSign.ofRat_mul B D,
    ← FiniteSign.ofRat_mul H (B * D), FiniteSign.jump_ofRat]

/-- A rational sign which is nonzero at the endpoint and has positive product
with its nearby value is stable in the finite sign table. -/
theorem finiteSign_stable_of_eq_zero_or_mul_pos {x₀ x₁ : ℚ}
    (h : x₀ = 0 ∨ 0 < x₀ * x₁) :
    FiniteSign.Stable (FiniteSign.ofRat x₀) (FiniteSign.ofRat x₁) := by
  rcases h with rfl | hpos
  · exact Or.inl rfl
  · apply Or.inr
    apply FiniteSign.value_injective
    rw [FiniteSign.value_ofRat, FiniteSign.value_ofRat]
    exact ratSign_eq_of_mul_pos hpos

/-- Rational complex multiplication always satisfies the deliberately coarse
finite sign relation used by the exhaustive table. -/
theorem finiteSign_complexProductCompatible
    (A B C D : ℚ) :
    FiniteSign.ComplexProductCompatible
      (FiniteSign.ofRat A) (FiniteSign.ofRat B)
      (FiniteSign.ofRat C) (FiniteSign.ofRat D)
      (FiniteSign.ofRat (A * C - B * D))
      (FiniteSign.ofRat (A * D + B * C)) := by
  constructor
  · simpa only [sub_eq_add_neg, FiniteSign.ofRat_mul,
      FiniteSign.ofRat_neg] using
      FiniteSign.sumCompatible_ofRat (A * C) (-(B * D))
  · simpa only [FiniteSign.ofRat_mul] using
      FiniteSign.sumCompatible_ofRat (A * D) (B * C)

/-- Rational specialization of the exhaustive local product sign table.  It
is the algebraic core used on a sufficiently refined cell containing one
possible left-endpoint pole and no other denominator event. -/
theorem rationalLocalProductTable
    (A₀ B₀ C₀ D₀ A₁ B₁ C₁ D₁ : ℚ)
    (hfactor₀ : A₀ ≠ 0 ∨ B₀ ≠ 0)
    (hfactor₁ : C₀ ≠ 0 ∨ D₀ ≠ 0)
    (hB₁ : B₁ ≠ 0) (hD₁ : D₁ ≠ 0)
    (hH₁ : A₁ * D₁ + B₁ * C₁ ≠ 0)
    (hA : A₀ = 0 ∨ 0 < A₀ * A₁)
    (hB : B₀ = 0 ∨ 0 < B₀ * B₁)
    (hC : C₀ = 0 ∨ 0 < C₀ * C₁)
    (hD : D₀ = 0 ∨ 0 < D₀ * D₁)
    (hE : A₀ * C₀ - B₀ * D₀ = 0 ∨
      0 < (A₀ * C₀ - B₀ * D₀) * (A₁ * C₁ - B₁ * D₁))
    (hH : A₀ * D₀ + B₀ * C₀ = 0 ∨
      0 < (A₀ * D₀ + B₀ * C₀) * (A₁ * D₁ + B₁ * C₁)) :
    leftEndpointIndex2
        (A₀ * C₀ - B₀ * D₀) (A₀ * D₀ + B₀ * C₀)
        (A₁ * C₁ - B₁ * D₁) (A₁ * D₁ + B₁ * C₁) =
      leftEndpointIndex2 A₀ B₀ A₁ B₁ +
        leftEndpointIndex2 C₀ D₀ C₁ D₁ -
        (signJump 1
          ((A₀ * D₀ + B₀ * C₀) * (B₀ * D₀)) : ℤ) +
        signJump 1 ((A₁ * D₁ + B₁ * C₁) * (B₁ * D₁)) := by
  let A₀s := FiniteSign.ofRat A₀
  let B₀s := FiniteSign.ofRat B₀
  let C₀s := FiniteSign.ofRat C₀
  let D₀s := FiniteSign.ofRat D₀
  let E₀s := FiniteSign.ofRat (A₀ * C₀ - B₀ * D₀)
  let H₀s := FiniteSign.ofRat (A₀ * D₀ + B₀ * C₀)
  let A₁s := FiniteSign.ofRat A₁
  let B₁s := FiniteSign.ofRat B₁
  let C₁s := FiniteSign.ofRat C₁
  let D₁s := FiniteSign.ofRat D₁
  let E₁s := FiniteSign.ofRat (A₁ * C₁ - B₁ * D₁)
  let H₁s := FiniteSign.ofRat (A₁ * D₁ + B₁ * C₁)
  have hadmissible : FiniteSign.LocalProductAdmissible
      A₀s B₀s C₀s D₀s E₀s H₀s A₁s B₁s C₁s D₁s E₁s H₁s := by
    refine ⟨?_, ?_, ?_, ?_, ?_, ?_, ?_, ?_, ?_, ?_, ?_, ?_, ?_⟩
    · simpa [A₀s, B₀s, FiniteSign.ofRat_eq_zero_iff] using hfactor₀
    · simpa [C₀s, D₀s, FiniteSign.ofRat_eq_zero_iff] using hfactor₁
    · simpa [B₁s, FiniteSign.ofRat_eq_zero_iff] using hB₁
    · simpa [D₁s, FiniteSign.ofRat_eq_zero_iff] using hD₁
    · simpa [H₁s, FiniteSign.ofRat_eq_zero_iff] using hH₁
    · exact finiteSign_stable_of_eq_zero_or_mul_pos hA
    · exact finiteSign_stable_of_eq_zero_or_mul_pos hB
    · exact finiteSign_stable_of_eq_zero_or_mul_pos hC
    · exact finiteSign_stable_of_eq_zero_or_mul_pos hD
    · exact finiteSign_stable_of_eq_zero_or_mul_pos hE
    · exact finiteSign_stable_of_eq_zero_or_mul_pos hH
    · exact finiteSign_complexProductCompatible A₀ B₀ C₀ D₀
    · exact finiteSign_complexProductCompatible A₁ B₁ C₁ D₁
  have htable := FiniteSign.localProductTable
    A₀s B₀s C₀s D₀s E₀s H₀s A₁s B₁s C₁s D₁s E₁s H₁s hadmissible
  dsimp only [A₀s, B₀s, C₀s, D₀s, E₀s, H₀s,
    A₁s, B₁s, C₁s, D₁s, E₁s, H₁s] at htable
  simpa only [FiniteSign.LocalProductIdentity,
    finiteSign_leftEndpointIndex2_ofRat,
    finiteSign_productCorrection2_ofRat] using htable

/-- If the three Cauchy chains on one refined cell have been reduced to their
left-endpoint pole contributions, the exhaustive rational sign table proves
the complete auxiliary product formula on that cell. -/
theorem auxiliaryProductFormula_of_localEndpointData
    (A B C D : RatPolynomial) (a b : ℚ)
    (hleft : cauchyIndex2 A B a b =
      leftEndpointIndex2 (A.eval a) (B.eval a) (A.eval b) (B.eval b))
    (hright : cauchyIndex2 C D a b =
      leftEndpointIndex2 (C.eval a) (D.eval a) (C.eval b) (D.eval b))
    (hproduct : cauchyIndex2 (productNumerator A B C D)
        (productDenominator A B C D) a b =
      leftEndpointIndex2
        ((productNumerator A B C D).eval a)
        ((productDenominator A B C D).eval a)
        ((productNumerator A B C D).eval b)
        ((productDenominator A B C D).eval b))
    (hfactorLeft : A.eval a ≠ 0 ∨ B.eval a ≠ 0)
    (hfactorRight : C.eval a ≠ 0 ∨ D.eval a ≠ 0)
    (hB : B.eval b ≠ 0) (hD : D.eval b ≠ 0)
    (hproductDenominator : (productDenominator A B C D).eval b ≠ 0)
    (hAstable : A.eval a = 0 ∨ 0 < A.eval a * A.eval b)
    (hBstable : B.eval a = 0 ∨ 0 < B.eval a * B.eval b)
    (hCstable : C.eval a = 0 ∨ 0 < C.eval a * C.eval b)
    (hDstable : D.eval a = 0 ∨ 0 < D.eval a * D.eval b)
    (hNumeratorStable :
      (productNumerator A B C D).eval a = 0 ∨
        0 < (productNumerator A B C D).eval a *
          (productNumerator A B C D).eval b)
    (hDenominatorStable :
      (productDenominator A B C D).eval a = 0 ∨
        0 < (productDenominator A B C D).eval a *
          (productDenominator A B C D).eval b) :
    AuxiliaryProductFormula A B C D a b := by
  rw [AuxiliaryProductFormula, hleft, hright, hproduct,
    auxiliaryEndpointCorrection2_eq_signJump,
    auxiliaryEndpointCorrection2_eq_signJump]
  simpa only [eval_productNumerator, eval_productDenominator] using
    rationalLocalProductTable
      (A.eval a) (B.eval a) (C.eval a) (D.eval a)
      (A.eval b) (B.eval b) (C.eval b) (D.eval b)
      hfactorLeft hfactorRight hB hD
      (by simpa only [eval_productDenominator] using hproductDenominator)
      hAstable hBstable hCstable hDstable
      (by simpa only [eval_productNumerator] using hNumeratorStable)
      (by simpa only [eval_productDenominator] using hDenominatorStable)

/-- Packaged proof data for a one-sided event located at the left rational
endpoint of a cell. -/
structure LocalEndpointData
    (A B C D : RatPolynomial) (a b : ℚ) : Type where
  leftIndex : cauchyIndex2 A B a b =
    leftEndpointIndex2 (A.eval a) (B.eval a) (A.eval b) (B.eval b)
  rightIndex : cauchyIndex2 C D a b =
    leftEndpointIndex2 (C.eval a) (D.eval a) (C.eval b) (D.eval b)
  productIndex : cauchyIndex2 (productNumerator A B C D)
      (productDenominator A B C D) a b =
    leftEndpointIndex2
      ((productNumerator A B C D).eval a)
      ((productDenominator A B C D).eval a)
      ((productNumerator A B C D).eval b)
      ((productDenominator A B C D).eval b)
  factorLeft : A.eval a ≠ 0 ∨ B.eval a ≠ 0
  factorRight : C.eval a ≠ 0 ∨ D.eval a ≠ 0
  rightB : B.eval b ≠ 0
  rightD : D.eval b ≠ 0
  rightProductDenominator : (productDenominator A B C D).eval b ≠ 0
  stableA : A.eval a = 0 ∨ 0 < A.eval a * A.eval b
  stableB : B.eval a = 0 ∨ 0 < B.eval a * B.eval b
  stableC : C.eval a = 0 ∨ 0 < C.eval a * C.eval b
  stableD : D.eval a = 0 ∨ 0 < D.eval a * D.eval b
  stableProductNumerator :
    (productNumerator A B C D).eval a = 0 ∨
      0 < (productNumerator A B C D).eval a *
        (productNumerator A B C D).eval b
  stableProductDenominator :
    (productDenominator A B C D).eval a = 0 ∨
      0 < (productDenominator A B C D).eval a *
        (productDenominator A B C D).eval b

/-- The packaged one-sided endpoint data discharges the local formula. -/
theorem LocalEndpointData.auxiliaryProductFormula
    {A B C D : RatPolynomial} {a b : ℚ}
    (data : LocalEndpointData A B C D a b) :
    AuxiliaryProductFormula A B C D a b :=
  auxiliaryProductFormula_of_localEndpointData A B C D a b
    data.leftIndex data.rightIndex data.productIndex
    data.factorLeft data.factorRight data.rightB data.rightD
    data.rightProductDenominator data.stableA data.stableB
    data.stableC data.stableD data.stableProductNumerator
    data.stableProductDenominator

/-- Decidable conjunction underlying a one-sided endpoint certificate. -/
def LocalEndpointConditions
    (A B C D : RatPolynomial) (a b : ℚ) : Prop :=
  cauchyIndex2 A B a b =
      leftEndpointIndex2 (A.eval a) (B.eval a) (A.eval b) (B.eval b) ∧
  cauchyIndex2 C D a b =
      leftEndpointIndex2 (C.eval a) (D.eval a) (C.eval b) (D.eval b) ∧
  cauchyIndex2 (productNumerator A B C D)
      (productDenominator A B C D) a b =
      leftEndpointIndex2
        ((productNumerator A B C D).eval a)
        ((productDenominator A B C D).eval a)
        ((productNumerator A B C D).eval b)
        ((productDenominator A B C D).eval b) ∧
  (A.eval a ≠ 0 ∨ B.eval a ≠ 0) ∧
  (C.eval a ≠ 0 ∨ D.eval a ≠ 0) ∧
  B.eval b ≠ 0 ∧ D.eval b ≠ 0 ∧
  (productDenominator A B C D).eval b ≠ 0 ∧
  (A.eval a = 0 ∨ 0 < A.eval a * A.eval b) ∧
  (B.eval a = 0 ∨ 0 < B.eval a * B.eval b) ∧
  (C.eval a = 0 ∨ 0 < C.eval a * C.eval b) ∧
  (D.eval a = 0 ∨ 0 < D.eval a * D.eval b) ∧
  ((productNumerator A B C D).eval a = 0 ∨
    0 < (productNumerator A B C D).eval a *
      (productNumerator A B C D).eval b) ∧
  ((productDenominator A B C D).eval a = 0 ∨
    0 < (productDenominator A B C D).eval a *
      (productDenominator A B C D).eval b)

instance (A B C D : RatPolynomial) (a b : ℚ) :
    Decidable (LocalEndpointConditions A B C D a b) := by
  unfold LocalEndpointConditions
  infer_instance

/-- Proof-bearing executable classifier for a one-sided rational endpoint
event. -/
def localEndpointData?
    (A B C D : RatPolynomial) (a b : ℚ) :
    Option (LocalEndpointData A B C D a b) :=
  if h : LocalEndpointConditions A B C D a b then
    let ⟨leftIndex, rightIndex, productIndex, factorLeft, factorRight,
      rightB, rightD, rightProductDenominator, stableA, stableB, stableC,
      stableD, stableProductNumerator, stableProductDenominator⟩ := h
    some
      { leftIndex, rightIndex, productIndex, factorLeft, factorRight,
        rightB, rightD, rightProductDenominator, stableA, stableB, stableC,
        stableD, stableProductNumerator, stableProductDenominator }
  else none

theorem localEndpointData?_isSome_of_conditions
    {A B C D : RatPolynomial} {a b : ℚ}
    (h : LocalEndpointConditions A B C D a b) :
    (localEndpointData? A B C D a b).isSome := by
  rw [localEndpointData?]
  split
  · rename_i hconditions
    rcases hconditions with ⟨leftIndex, rightIndex, productIndex,
      factorLeft, factorRight, rightB, rightD, rightProductDenominator,
      stableA, stableB, stableC, stableD, stableProductNumerator,
      stableProductDenominator⟩
    rfl
  · rename_i hconditions
    exact (hconditions h).elim

/-! ## Two-sided isolated-event certificates -/

/-- The six signs attached to one formal product event. -/
structure EventSigns where
  factorLeftReal : FiniteSign
  factorLeftImag : FiniteSign
  factorRightReal : FiniteSign
  factorRightImag : FiniteSign
  productReal : FiniteSign
  productImag : FiniteSign
deriving DecidableEq, Repr

/-- Formal center signs for a cell on which all six coordinate signs are
stable: use the exact signs at the left rational endpoint. -/
def stableEventSigns
    (A B C D : RatPolynomial) (a : ℚ) : EventSigns where
  factorLeftReal := FiniteSign.ofRat (A.eval a)
  factorLeftImag := FiniteSign.ofRat (B.eval a)
  factorRightReal := FiniteSign.ofRat (C.eval a)
  factorRightImag := FiniteSign.ofRat (D.eval a)
  productReal := FiniteSign.ofRat ((productNumerator A B C D).eval a)
  productImag := FiniteSign.ofRat ((productDenominator A B C D).eval a)

namespace EventSigns

/-- Decidable conditions saying that six formal event signs classify all
three Cauchy indices on one rational cell and are compatible with the two
rational endpoint sign records. -/
def Certifies
    (signs : EventSigns) (A B C D : RatPolynomial) (a b : ℚ) : Prop :=
  FiniteSign.LocalProductAdmissible
    signs.factorLeftReal signs.factorLeftImag
    signs.factorRightReal signs.factorRightImag
    signs.productReal signs.productImag
    (FiniteSign.ofRat (A.eval a)) (FiniteSign.ofRat (B.eval a))
    (FiniteSign.ofRat (C.eval a)) (FiniteSign.ofRat (D.eval a))
    (FiniteSign.ofRat ((productNumerator A B C D).eval a))
    (FiniteSign.ofRat ((productDenominator A B C D).eval a)) ∧
  FiniteSign.LocalProductAdmissible
      signs.factorLeftReal signs.factorLeftImag
      signs.factorRightReal signs.factorRightImag
      signs.productReal signs.productImag
      (FiniteSign.ofRat (A.eval b)) (FiniteSign.ofRat (B.eval b))
      (FiniteSign.ofRat (C.eval b)) (FiniteSign.ofRat (D.eval b))
      (FiniteSign.ofRat ((productNumerator A B C D).eval b))
      (FiniteSign.ofRat ((productDenominator A B C D).eval b)) ∧
  cauchyIndex2 A B a b =
      FiniteSign.eventIndex2
        signs.factorLeftReal signs.factorLeftImag
        (FiniteSign.ofRat (A.eval a)) (FiniteSign.ofRat (B.eval a))
        (FiniteSign.ofRat (A.eval b)) (FiniteSign.ofRat (B.eval b)) ∧
  cauchyIndex2 C D a b =
      FiniteSign.eventIndex2
        signs.factorRightReal signs.factorRightImag
        (FiniteSign.ofRat (C.eval a)) (FiniteSign.ofRat (D.eval a))
        (FiniteSign.ofRat (C.eval b)) (FiniteSign.ofRat (D.eval b)) ∧
  cauchyIndex2 (productNumerator A B C D)
      (productDenominator A B C D) a b =
    FiniteSign.eventIndex2 signs.productReal signs.productImag
      (FiniteSign.ofRat ((productNumerator A B C D).eval a))
      (FiniteSign.ofRat ((productDenominator A B C D).eval a))
      (FiniteSign.ofRat ((productNumerator A B C D).eval b))
      (FiniteSign.ofRat ((productDenominator A B C D).eval b))

instance (signs : EventSigns) (A B C D : RatPolynomial) (a b : ℚ) :
    Decidable (signs.Certifies A B C D a b) := by
  unfold Certifies
  infer_instance

end EventSigns

/-- Finite proof data for one rational cell surrounding a single formal
event.  The event itself is only a six-sign record, never a completed or
rational parameter value. -/
structure LocalEventData
    (A B C D : RatPolynomial) (a b : ℚ) where
  signs : EventSigns
  certifies : signs.Certifies A B C D a b

/-- Decidable checker for one proposed six-sign event record. -/
def localEventDataCheck
    (A B C D : RatPolynomial) (a b : ℚ) (signs : EventSigns) : Bool :=
  decide (signs.Certifies A B C D a b)

theorem EventSigns.certifies_of_check
    {A B C D : RatPolynomial} {a b : ℚ} {signs : EventSigns}
    (hcheck : localEventDataCheck A B C D a b signs = true) :
    signs.Certifies A B C D a b := by
  change decide (signs.Certifies A B C D a b) = true at hcheck
  exact of_decide_eq_true hcheck

/-- Canonical executable enumeration of the three finite signs. -/
def finiteSignCandidates : List FiniteSign :=
  [.negative, .zero, .positive]

theorem mem_finiteSignCandidates (sign : FiniteSign) :
    sign ∈ finiteSignCandidates := by
  cases sign <;> simp [finiteSignCandidates]

/-- Canonical executable enumeration of the `3^6 = 729` formal event
records.  The nested list program avoids conversion through sparse arithmetic from a
finite set. -/
def eventSignCandidates : List EventSigns :=
  finiteSignCandidates.flatMap fun factorLeftReal =>
  finiteSignCandidates.flatMap fun factorLeftImag =>
  finiteSignCandidates.flatMap fun factorRightReal =>
  finiteSignCandidates.flatMap fun factorRightImag =>
  finiteSignCandidates.flatMap fun productReal =>
  finiteSignCandidates.map fun productImag =>
    { factorLeftReal, factorLeftImag, factorRightReal, factorRightImag,
      productReal, productImag }

theorem mem_eventSignCandidates (signs : EventSigns) :
    signs ∈ eventSignCandidates := by
  rcases signs with ⟨factorLeftReal, factorLeftImag, factorRightReal,
    factorRightImag, productReal, productImag⟩
  simp only [eventSignCandidates, List.mem_flatMap, List.mem_map]
  exact ⟨factorLeftReal, mem_finiteSignCandidates factorLeftReal,
    factorLeftImag, mem_finiteSignCandidates factorLeftImag,
    factorRightReal, mem_finiteSignCandidates factorRightReal,
    factorRightImag, mem_finiteSignCandidates factorRightImag,
    productReal, mem_finiteSignCandidates productReal,
    productImag, mem_finiteSignCandidates productImag, rfl⟩

/-- Exhaustive executable search for a formal event record classifying one
rational cell. -/
def localEventSigns?
    (A B C D : RatPolynomial) (a b : ℚ) : Option EventSigns :=
  eventSignCandidates.find? fun signs =>
    localEventDataCheck A B C D a b signs

theorem localEventSigns?_some_certifies
    {A B C D : RatPolynomial} {a b : ℚ} {signs : EventSigns}
    (hsearch : localEventSigns? A B C D a b = some signs) :
    signs.Certifies A B C D a b := by
  apply EventSigns.certifies_of_check
  exact List.find?_some hsearch

/-- If any six-sign record classifies the cell, exhaustive search returns a
record. -/
theorem localEventSigns?_isSome_of_certifies
    {A B C D : RatPolynomial} {a b : ℚ} (signs : EventSigns)
    (hcertifies : signs.Certifies A B C D a b) :
    (localEventSigns? A B C D a b).isSome := by
  rw [localEventSigns?, List.find?_isSome]
  refine ⟨signs, ?_, ?_⟩
  · exact mem_eventSignCandidates signs
  · simp [localEventDataCheck, hcertifies]

/-- Proof-bearing executable local-event classifier. -/
irreducible_def localEventData?
    (A B C D : RatPolynomial) (a b : ℚ) :
    Option (LocalEventData A B C D a b) :=
  match hsearch : localEventSigns? A B C D a b with
  | none => none
  | some signs => some
      { signs
        certifies := localEventSigns?_some_certifies hsearch }

theorem localEventData?_isSome
    (A B C D : RatPolynomial) (a b : ℚ) :
    (localEventData? A B C D a b).isSome =
      (localEventSigns? A B C D a b).isSome := by
  rw [localEventData?_def]
  split <;> rename_i hsearch <;>
    simp only [hsearch, Option.isSome_none, Option.isSome_some]

/-- Stable endpoint signs and zero local Cauchy indices produce a valid
formal no-event record.  This is the local classifier used away from the
finite union of signed-chain events. -/
theorem stableEventSigns_certifies
    {A B C D : RatPolynomial} {a b : ℚ}
    (hleftIndex : cauchyIndex2 A B a b = 0)
    (hrightIndex : cauchyIndex2 C D a b = 0)
    (hproductIndex : cauchyIndex2 (productNumerator A B C D)
      (productDenominator A B C D) a b = 0)
    (hfactorLeft : A.eval a ≠ 0 ∨ B.eval a ≠ 0)
    (hfactorRight : C.eval a ≠ 0 ∨ D.eval a ≠ 0)
    (hBa : B.eval a ≠ 0) (hDa : D.eval a ≠ 0)
    (hHa : (productDenominator A B C D).eval a ≠ 0)
    (hBb : B.eval b ≠ 0) (hDb : D.eval b ≠ 0)
    (hHb : (productDenominator A B C D).eval b ≠ 0)
    (hA : A.eval a = 0 ∨ 0 < A.eval a * A.eval b)
    (hB : B.eval a = 0 ∨ 0 < B.eval a * B.eval b)
    (hC : C.eval a = 0 ∨ 0 < C.eval a * C.eval b)
    (hD : D.eval a = 0 ∨ 0 < D.eval a * D.eval b)
    (hE : (productNumerator A B C D).eval a = 0 ∨
      0 < (productNumerator A B C D).eval a *
        (productNumerator A B C D).eval b)
    (hH : (productDenominator A B C D).eval a = 0 ∨
      0 < (productDenominator A B C D).eval a *
        (productDenominator A B C D).eval b) :
    (stableEventSigns A B C D a).Certifies A B C D a b := by
  have hBaSign : FiniteSign.ofRat (B.eval a) ≠ FiniteSign.zero := by
    simpa [FiniteSign.ofRat_eq_zero_iff] using hBa
  have hDaSign : FiniteSign.ofRat (D.eval a) ≠ FiniteSign.zero := by
    simpa [FiniteSign.ofRat_eq_zero_iff] using hDa
  have hHaSign :
      FiniteSign.ofRat ((productDenominator A B C D).eval a) ≠
        FiniteSign.zero := by
    simpa [FiniteSign.ofRat_eq_zero_iff] using hHa
  unfold EventSigns.Certifies
  refine ⟨?_, ?_, ?_, ?_, ?_⟩
  · refine ⟨?_, ?_, hBaSign, hDaSign, hHaSign,
      Or.inr rfl, Or.inr rfl, Or.inr rfl, Or.inr rfl,
      Or.inr rfl, Or.inr rfl, ?_, ?_⟩
    · simpa [stableEventSigns, FiniteSign.ofRat_eq_zero_iff] using
        hfactorLeft
    · simpa [stableEventSigns, FiniteSign.ofRat_eq_zero_iff] using
        hfactorRight
    · simpa only [stableEventSigns, eval_productNumerator,
        eval_productDenominator] using
        finiteSign_complexProductCompatible
          (A.eval a) (B.eval a) (C.eval a) (D.eval a)
    · simpa only [eval_productNumerator, eval_productDenominator] using
        finiteSign_complexProductCompatible
          (A.eval a) (B.eval a) (C.eval a) (D.eval a)
  · refine ⟨?_, ?_, ?_, ?_, ?_, ?_, ?_, ?_, ?_, ?_, ?_, ?_, ?_⟩
    · simpa [stableEventSigns, FiniteSign.ofRat_eq_zero_iff] using
        hfactorLeft
    · simpa [stableEventSigns, FiniteSign.ofRat_eq_zero_iff] using
        hfactorRight
    · simpa [FiniteSign.ofRat_eq_zero_iff] using hBb
    · simpa [FiniteSign.ofRat_eq_zero_iff] using hDb
    · simpa [FiniteSign.ofRat_eq_zero_iff] using hHb
    · exact finiteSign_stable_of_eq_zero_or_mul_pos hA
    · exact finiteSign_stable_of_eq_zero_or_mul_pos hB
    · exact finiteSign_stable_of_eq_zero_or_mul_pos hC
    · exact finiteSign_stable_of_eq_zero_or_mul_pos hD
    · exact finiteSign_stable_of_eq_zero_or_mul_pos hE
    · exact finiteSign_stable_of_eq_zero_or_mul_pos hH
    · simpa only [stableEventSigns, eval_productNumerator,
        eval_productDenominator] using
        finiteSign_complexProductCompatible
          (A.eval a) (B.eval a) (C.eval a) (D.eval a)
    · simpa only [eval_productNumerator, eval_productDenominator] using
        finiteSign_complexProductCompatible
          (A.eval b) (B.eval b) (C.eval b) (D.eval b)
  · rw [hleftIndex]
    simp only [stableEventSigns, FiniteSign.eventIndex2,
      FiniteSign.leftEndpointIndex2, hBaSign, if_false, sub_self]
  · rw [hrightIndex]
    simp only [stableEventSigns, FiniteSign.eventIndex2,
      FiniteSign.leftEndpointIndex2, hDaSign, if_false, sub_self]
  · rw [hproductIndex]
    simp only [stableEventSigns, FiniteSign.eventIndex2,
      FiniteSign.leftEndpointIndex2, hHaSign, if_false, sub_self]

/-- Any displayed certifying event record makes the proof-bearing exhaustive
classifier succeed. -/
theorem localEventData?_isSome_of_certifies
    {A B C D : RatPolynomial} {a b : ℚ} (signs : EventSigns)
    (hcertifies : signs.Certifies A B C D a b) :
    (localEventData? A B C D a b).isSome := by
  have hsearch := localEventSigns?_isSome_of_certifies signs hcertifies
  rw [localEventData?_isSome]
  exact hsearch

/-- A two-sided isolated-event certificate proves the complete auxiliary
product formula on its rational cell. -/
theorem LocalEventData.auxiliaryProductFormula
    {A B C D : RatPolynomial} {a b : ℚ}
    (data : LocalEventData A B C D a b) :
    AuxiliaryProductFormula A B C D a b := by
  rcases data.certifies with
    ⟨hleftAdmissible, hrightAdmissible, hleftIndex,
      hrightIndex, hproductIndex⟩
  have htable := FiniteSign.localProductEventTable
    data.signs.factorLeftReal data.signs.factorLeftImag
    data.signs.factorRightReal data.signs.factorRightImag
    data.signs.productReal data.signs.productImag
    (FiniteSign.ofRat (A.eval a)) (FiniteSign.ofRat (B.eval a))
    (FiniteSign.ofRat (C.eval a)) (FiniteSign.ofRat (D.eval a))
    (FiniteSign.ofRat ((productNumerator A B C D).eval a))
    (FiniteSign.ofRat ((productDenominator A B C D).eval a))
    (FiniteSign.ofRat (A.eval b)) (FiniteSign.ofRat (B.eval b))
    (FiniteSign.ofRat (C.eval b)) (FiniteSign.ofRat (D.eval b))
    (FiniteSign.ofRat ((productNumerator A B C D).eval b))
    (FiniteSign.ofRat ((productDenominator A B C D).eval b))
    hleftAdmissible hrightAdmissible
  rw [AuxiliaryProductFormula, hleftIndex, hrightIndex, hproductIndex,
    auxiliaryEndpointCorrection2_eq_signJump,
    auxiliaryEndpointCorrection2_eq_signJump]
  simpa only [FiniteSign.LocalEventProductIdentity,
    finiteSign_productCorrection2_ofRat,
    eval_productNumerator, eval_productDenominator] using htable

/-- Every proof-bearing result of the executable classifier is a sound local
product-formula certificate. -/
theorem localEventData?_some_auxiliaryProductFormula
    {A B C D : RatPolynomial} {a b : ℚ}
    {data : LocalEventData A B C D a b}
    (_hsearch : localEventData? A B C D a b = some data) :
    AuxiliaryProductFormula A B C D a b :=
  data.auxiliaryProductFormula

/-! ## Finite simultaneous product-event partitions -/

/-- A finite proof tree covering an oriented rational interval.  Leaves are
either one-sided rational endpoint events or two-sided formal events; split
nodes compose adjacent cells and reverse nodes cover right-endpoint events.
No leaf stores the desired product formula itself. -/
inductive AuxiliaryProductPartition
    (A B C D : RatPolynomial) : ℚ → ℚ → Type
  | refl (a : ℚ) : AuxiliaryProductPartition A B C D a a
  | endpoint {a b : ℚ} (data : LocalEndpointData A B C D a b) :
      AuxiliaryProductPartition A B C D a b
  | event {a b : ℚ} (data : LocalEventData A B C D a b) :
      AuxiliaryProductPartition A B C D a b
  | split {a b c : ℚ}
      (left : AuxiliaryProductPartition A B C D a b)
      (right : AuxiliaryProductPartition A B C D b c) :
      AuxiliaryProductPartition A B C D a c
  | reverse {a b : ℚ}
      (forward : AuxiliaryProductPartition A B C D a b) :
      AuxiliaryProductPartition A B C D b a

namespace AuxiliaryProductPartition

/-- Soundness of a finite simultaneous product-event partition. -/
theorem auxiliaryProductFormula
    {A B C D : RatPolynomial} {a b : ℚ}
    (partition : AuxiliaryProductPartition A B C D a b) :
    AuxiliaryProductFormula A B C D a b := by
  induction partition with
  | refl a => exact auxiliaryProductFormula_refl A B C D a
  | endpoint data => exact data.auxiliaryProductFormula
  | event data => exact data.auxiliaryProductFormula
  | split left right leftFormula rightFormula =>
      exact leftFormula.add rightFormula
  | reverse forward forwardFormula => exact forwardFormula.reverse

end AuxiliaryProductPartition

/-- Executable classifier for one complete partition leaf.  It first searches
for a two-sided formal event, then tries a left rational endpoint event, and
finally the reversed right-endpoint case. -/
irreducible_def localProductLeaf?
    (A B C D : RatPolynomial) (a b : ℚ) :
    Option (AuxiliaryProductPartition A B C D a b) :=
  match localEventData? A B C D a b with
  | some data => some (.event data)
  | none =>
      match localEndpointData? A B C D a b with
      | some data => some (.endpoint data)
      | none =>
          match localEndpointData? A B C D b a with
          | some data => some (.reverse (.endpoint data))
          | none => none

/-- Every returned executable leaf proves the auxiliary product formula. -/
theorem localProductLeaf?_some_auxiliaryProductFormula
    {A B C D : RatPolynomial} {a b : ℚ}
    {partition : AuxiliaryProductPartition A B C D a b}
    (_hleaf : localProductLeaf? A B C D a b = some partition) :
    AuxiliaryProductFormula A B C D a b :=
  partition.auxiliaryProductFormula

/-- Consequently the combined executable leaf classifier accepts every
stable zero-index cell. -/
theorem localProductLeaf?_isSome_of_stable
    {A B C D : RatPolynomial} {a b : ℚ}
    (hleftIndex : cauchyIndex2 A B a b = 0)
    (hrightIndex : cauchyIndex2 C D a b = 0)
    (hproductIndex : cauchyIndex2 (productNumerator A B C D)
      (productDenominator A B C D) a b = 0)
    (hfactorLeft : A.eval a ≠ 0 ∨ B.eval a ≠ 0)
    (hfactorRight : C.eval a ≠ 0 ∨ D.eval a ≠ 0)
    (hBa : B.eval a ≠ 0) (hDa : D.eval a ≠ 0)
    (hHa : (productDenominator A B C D).eval a ≠ 0)
    (hBb : B.eval b ≠ 0) (hDb : D.eval b ≠ 0)
    (hHb : (productDenominator A B C D).eval b ≠ 0)
    (hA : A.eval a = 0 ∨ 0 < A.eval a * A.eval b)
    (hB : B.eval a = 0 ∨ 0 < B.eval a * B.eval b)
    (hC : C.eval a = 0 ∨ 0 < C.eval a * C.eval b)
    (hD : D.eval a = 0 ∨ 0 < D.eval a * D.eval b)
    (hE : (productNumerator A B C D).eval a = 0 ∨
      0 < (productNumerator A B C D).eval a *
        (productNumerator A B C D).eval b)
    (hH : (productDenominator A B C D).eval a = 0 ∨
      0 < (productDenominator A B C D).eval a *
        (productDenominator A B C D).eval b) :
    (localProductLeaf? A B C D a b).isSome := by
  have hdata := localEventData?_isSome_of_certifies
    (stableEventSigns A B C D a)
    (stableEventSigns_certifies hleftIndex hrightIndex hproductIndex
      hfactorLeft hfactorRight hBa hDa hHa hBb hDb hHb
      hA hB hC hD hE hH)
  rcases Option.isSome_iff_exists.mp hdata with ⟨data, hdata⟩
  rw [localProductLeaf?_def, hdata]
  rfl

/-- Three neutral complete signed chains and six coefficient-resolved
coordinate polynomials provide all data required by the stable product-leaf
classifier. -/
theorem localProductLeaf?_isSome_of_neutralChains
    {A B C D : RatPolynomial}
    {interval : FTA.SturmTransducer.RationalInterval}
    (proper : interval.Proper)
    (leftChain : FTA.SturmTransducer.NeutralChainCertificates interval
      (cauchyChain A B))
    (rightChain : FTA.SturmTransducer.NeutralChainCertificates interval
      (cauchyChain C D))
    (productChain : FTA.SturmTransducer.NeutralChainCertificates interval
      (cauchyChain (productNumerator A B C D)
        (productDenominator A B C D)))
    (hA : FTA.SturmTransducer.MidpointResolved interval A)
    (hB : FTA.SturmTransducer.MidpointResolved interval B)
    (hC : FTA.SturmTransducer.MidpointResolved interval C)
    (hD : FTA.SturmTransducer.MidpointResolved interval D)
    (hE : FTA.SturmTransducer.MidpointResolved interval
      (productNumerator A B C D))
    (hH : FTA.SturmTransducer.MidpointResolved interval
      (productDenominator A B C D)) :
    (localProductLeaf? A B C D interval.lower interval.upper).isSome := by
  have hAEndpoints :=
    FTA.SturmTransducer.eval_lower_mul_eval_upper_pos_of_midpointResolved
      interval proper A hA
  have hBEndpoints :=
    FTA.SturmTransducer.eval_lower_mul_eval_upper_pos_of_midpointResolved
      interval proper B hB
  have hCEndpoints :=
    FTA.SturmTransducer.eval_lower_mul_eval_upper_pos_of_midpointResolved
      interval proper C hC
  have hDEndpoints :=
    FTA.SturmTransducer.eval_lower_mul_eval_upper_pos_of_midpointResolved
      interval proper D hD
  have hEEndpoints :=
    FTA.SturmTransducer.eval_lower_mul_eval_upper_pos_of_midpointResolved
      interval proper (productNumerator A B C D) hE
  have hHEndpoints :=
    FTA.SturmTransducer.eval_lower_mul_eval_upper_pos_of_midpointResolved
      interval proper (productDenominator A B C D) hH
  apply localProductLeaf?_isSome_of_stable
  · exact leftChain.cauchyIndex2_eq_zero
  · exact rightChain.cauchyIndex2_eq_zero
  · exact productChain.cauchyIndex2_eq_zero
  · exact Or.inl (left_ne_zero_of_mul hAEndpoints.ne')
  · exact Or.inl (left_ne_zero_of_mul hCEndpoints.ne')
  · exact left_ne_zero_of_mul hBEndpoints.ne'
  · exact left_ne_zero_of_mul hDEndpoints.ne'
  · exact left_ne_zero_of_mul hHEndpoints.ne'
  · exact right_ne_zero_of_mul hBEndpoints.ne'
  · exact right_ne_zero_of_mul hDEndpoints.ne'
  · exact right_ne_zero_of_mul hHEndpoints.ne'
  · exact Or.inr hAEndpoints
  · exact Or.inr hBEndpoints
  · exact Or.inr hCEndpoints
  · exact Or.inr hDEndpoints
  · exact Or.inr hEEndpoints
  · exact Or.inr hHEndpoints

/-- Formal center signs for one arbitrary gcd-reduced Cauchy pair, together
with stability at both rational endpoints and the exact represented index. -/
structure ReducedCauchyEventSigns
    (R S : RatPolynomial)
    (interval : FTA.SturmTransducer.RationalInterval) where
  numerator : FiniteSign
  denominator : FiniteSign
  nonzero : numerator ≠ .zero ∨ denominator ≠ .zero
  numeratorSource :
    (numerator = .zero ∧
      ¬FTA.SturmTransducer.MidpointResolved interval
        (reducedNumerator R S)) ∨
    ∃ _resolved : FTA.SturmTransducer.MidpointResolved interval
        (reducedNumerator R S),
      numerator = FiniteSign.ofRat
        ((reducedNumerator R S).eval interval.lower)
  denominatorSource :
    (denominator = .zero ∧
      ¬FTA.SturmTransducer.MidpointResolved interval
        (reducedDenominator R S)) ∨
    ∃ _resolved : FTA.SturmTransducer.MidpointResolved interval
        (reducedDenominator R S),
      denominator = FiniteSign.ofRat
        ((reducedDenominator R S).eval interval.lower)
  numeratorLowerStable : FiniteSign.Stable numerator
    (FiniteSign.ofRat ((reducedNumerator R S).eval interval.lower))
  denominatorLowerStable : FiniteSign.Stable denominator
    (FiniteSign.ofRat ((reducedDenominator R S).eval interval.lower))
  numeratorUpperStable : FiniteSign.Stable numerator
    (FiniteSign.ofRat ((reducedNumerator R S).eval interval.upper))
  denominatorUpperStable : FiniteSign.Stable denominator
    (FiniteSign.ofRat ((reducedDenominator R S).eval interval.upper))
  index : cauchyIndex2 R S interval.lower interval.upper =
    FiniteSign.eventIndex2 numerator denominator
      (FiniteSign.ofRat ((reducedNumerator R S).eval interval.lower))
      (FiniteSign.ofRat ((reducedDenominator R S).eval interval.lower))
      (FiniteSign.ofRat ((reducedNumerator R S).eval interval.upper))
      (FiniteSign.ofRat ((reducedDenominator R S).eval interval.upper))

/-- A successful midpoint margin fixes the endpoint sign to the exact sign at
the rational midpoint used by the executable test. -/
theorem finiteSign_ofRat_lower_eq_midpoint_of_midpointResolved
    (interval : FTA.SturmTransducer.RationalInterval)
    (proper : interval.Proper) (p : RatPolynomial)
    (resolved : FTA.SturmTransducer.MidpointResolved interval p) :
    FiniteSign.ofRat (p.eval interval.lower) =
      FiniteSign.ofRat
        (p.eval (midpoint interval.lower interval.upper)) := by
  let certificate :=
    FTA.SturmTransducer.midpointResolvedCertificate
      interval proper p resolved
  have hsame : 0 < p.eval interval.lower *
      p.eval (midpoint interval.lower interval.upper) :=
    certificate.eval_mul_pos_between le_rfl proper.le
      certificate.lowerLe certificate.leUpper
  apply FiniteSign.value_injective
  simp only [FiniteSign.value_ofRat]
  exact ratSign_eq_of_mul_pos hsame

namespace ReducedCauchyEventSigns

/-- The stored source decision is an exact executable description of the
formal reduced numerator: unresolved means formal zero, while resolved means
the genuine midpoint sign. -/
theorem numerator_eq_midpointIte
    {R S : RatPolynomial}
    {interval : FTA.SturmTransducer.RationalInterval}
    (data : ReducedCauchyEventSigns R S interval)
    (proper : interval.Proper) :
    data.numerator =
      if FTA.SturmTransducer.MidpointResolved interval
          (reducedNumerator R S) then
        FiniteSign.ofRat ((reducedNumerator R S).eval
          (midpoint interval.lower interval.upper))
      else .zero := by
  by_cases resolved : FTA.SturmTransducer.MidpointResolved interval
      (reducedNumerator R S)
  · rw [if_pos resolved]
    rcases data.numeratorSource with unresolved | ⟨sourceResolved, hsource⟩
    · exact (unresolved.2 resolved).elim
    · exact hsource.trans
        (finiteSign_ofRat_lower_eq_midpoint_of_midpointResolved
          interval proper (reducedNumerator R S) sourceResolved)
  · rw [if_neg resolved]
    rcases data.numeratorSource with unresolved | ⟨sourceResolved, _hsource⟩
    · exact unresolved.1
    · exact (resolved sourceResolved).elim

/-- Exact midpoint description of the formal reduced denominator. -/
theorem denominator_eq_midpointIte
    {R S : RatPolynomial}
    {interval : FTA.SturmTransducer.RationalInterval}
    (data : ReducedCauchyEventSigns R S interval)
    (proper : interval.Proper) :
    data.denominator =
      if FTA.SturmTransducer.MidpointResolved interval
          (reducedDenominator R S) then
        FiniteSign.ofRat ((reducedDenominator R S).eval
          (midpoint interval.lower interval.upper))
      else .zero := by
  by_cases resolved : FTA.SturmTransducer.MidpointResolved interval
      (reducedDenominator R S)
  · rw [if_pos resolved]
    rcases data.denominatorSource with unresolved | ⟨sourceResolved, hsource⟩
    · exact (unresolved.2 resolved).elim
    · exact hsource.trans
        (finiteSign_ofRat_lower_eq_midpoint_of_midpointResolved
          interval proper (reducedDenominator R S) sourceResolved)
  · rw [if_neg resolved]
    rcases data.denominatorSource with unresolved | ⟨sourceResolved, _hsource⟩
    · exact unresolved.1
    · exact (resolved sourceResolved).elim

end ReducedCauchyEventSigns

/-- The coefficient-computed complete-chain width constructs formal event
signs for either executable branch: a resolved first member gives a neutral
index, while an unresolved first member forces a resolved numerator and a
single first-pair contribution. -/
def reducedCauchyEventSignsOfRefinedWidth
    (R S : RatPolynomial) (hR : R.isZero = false) (hS : S.isZero = false)
    (root interval : FTA.SturmTransducer.RationalInterval)
    (hrefines : interval.Refines root) (proper : interval.Proper)
    (hwidth : interval.width <
      FTA.SturmTransducer.cauchyChainAmbientWidthResolution
        R S hR hS root) :
    ReducedCauchyEventSigns R S interval := by
  let p := reducedDenominator R S
  let q := reducedNumerator R S
  let coprime := FTA.SturmTransducer.reducedCauchyPairCertificate R S hR hS
  have hq : q.isZero = false := by
    simpa only [q] using reducedNumerator_isZero_false hR
  have hradius : FTA.RationalPolynomialBounds.intervalRadius
        interval.lower interval.upper
        (FTA.RationalPolynomialBounds.midpoint
          interval.lower interval.upper) <
      FTA.SturmTransducer.signedChainAmbientRadius p q coprime
        (FTA.RationalPolynomialBounds.intervalMagnitude
          root.lower root.upper) := by
    rw [interval.midpointRadius_eq_half_width proper]
    dsimp only [FTA.SturmTransducer.cauchyChainAmbientWidthResolution] at hwidth
    simpa only [p, q, coprime] using (show interval.width / 2 <
      FTA.SturmTransducer.signedChainAmbientRadius
        (reducedDenominator R S) (reducedNumerator R S)
        (FTA.SturmTransducer.reducedCauchyPairCertificate R S hR hS)
        (FTA.RationalPolynomialBounds.intervalMagnitude
          root.lower root.upper) by
          linarith)
  have bounds : FTA.SturmTransducer.NeutralChainResolutionBounds interval p
      (signedRemainderChain p q).tail :=
    FTA.SturmTransducer.signedChainResolutionBoundsOfAmbient
      root interval hrefines proper p q coprime hradius
  by_cases hpResolved : FTA.SturmTransducer.MidpointResolved interval p
  · have result :=
      FTA.SturmTransducer.neutralCauchyChainCertificates?_succeeds_of_refined_width
        R S hR hS root interval hrefines proper hwidth (by
          simpa only [p] using hpResolved)
    have hpEndpoints :=
      FTA.SturmTransducer.eval_lower_mul_eval_upper_pos_of_midpointResolved
        interval proper p hpResolved
    have hpLower : p.eval interval.lower ≠ 0 :=
      left_ne_zero_of_mul hpEndpoints.ne'
    have hpSign : FiniteSign.ofRat (p.eval interval.lower) ≠ .zero := by
      simpa [FiniteSign.ofRat_eq_zero_iff] using hpLower
    have hpStable : FiniteSign.Stable
        (FiniteSign.ofRat (p.eval interval.lower))
        (FiniteSign.ofRat (p.eval interval.upper)) :=
      finiteSign_stable_of_eq_zero_or_mul_pos (Or.inr hpEndpoints)
    let numeratorSign :=
      if FTA.SturmTransducer.MidpointResolved interval q then
        FiniteSign.ofRat (q.eval interval.lower)
      else .zero
    have hqLowerStable : FiniteSign.Stable numeratorSign
        (FiniteSign.ofRat (q.eval interval.lower)) := by
      by_cases hqResolved : FTA.SturmTransducer.MidpointResolved interval q
      · exact Or.inr (by simp [numeratorSign, hqResolved])
      · exact Or.inl (by simp [numeratorSign, hqResolved])
    have hqUpperStable : FiniteSign.Stable numeratorSign
        (FiniteSign.ofRat (q.eval interval.upper)) := by
      by_cases hqResolved : FTA.SturmTransducer.MidpointResolved interval q
      · have hqEndpoints :=
          FTA.SturmTransducer.eval_lower_mul_eval_upper_pos_of_midpointResolved
            interval proper q hqResolved
        simpa only [numeratorSign, hqResolved, ↓reduceIte] using
          finiteSign_stable_of_eq_zero_or_mul_pos (Or.inr hqEndpoints)
      · exact Or.inl (by simp [numeratorSign, hqResolved])
    have hqSource :
        (numeratorSign = .zero ∧
          ¬FTA.SturmTransducer.MidpointResolved interval q) ∨
        ∃ _resolved : FTA.SturmTransducer.MidpointResolved interval q,
          numeratorSign = FiniteSign.ofRat (q.eval interval.lower) := by
      by_cases hqResolved : FTA.SturmTransducer.MidpointResolved interval q
      · exact Or.inr ⟨hqResolved, by simp [numeratorSign, hqResolved]⟩
      · exact Or.inl ⟨by simp [numeratorSign, hqResolved], hqResolved⟩
    refine
      { numerator := numeratorSign
        denominator := FiniteSign.ofRat (p.eval interval.lower)
        nonzero := Or.inr hpSign
        numeratorSource := by simpa only [q] using hqSource
        denominatorSource := Or.inr ⟨by simpa only [p] using hpResolved, rfl⟩
        numeratorLowerStable := hqLowerStable
        denominatorLowerStable := Or.inr rfl
        numeratorUpperStable := hqUpperStable
        denominatorUpperStable := hpStable
        index := ?_ }
    have hindex := result.1.cauchyIndex2_eq_zero
    rw [hindex]
    simp only [FiniteSign.eventIndex2, FiniteSign.leftEndpointIndex2,
      hpSign, if_false, sub_self]
  · have boundsFromSecond := bounds
    rw [FTA.SturmTransducer.signedRemainderChain_tail_eq_of_second_nonzero
      p q hq] at boundsFromSecond
    have hqResolved : FTA.SturmTransducer.MidpointResolved interval q :=
      boundsFromSecond.secondResolvedOfFirstUnresolved proper hpResolved
    have hqEndpoints :=
      FTA.SturmTransducer.eval_lower_mul_eval_upper_pos_of_midpointResolved
        interval proper q hqResolved
    have hqLower : q.eval interval.lower ≠ 0 :=
      left_ne_zero_of_mul hqEndpoints.ne'
    have hqSign : FiniteSign.ofRat (q.eval interval.lower) ≠ .zero := by
      simpa [FiniteSign.ofRat_eq_zero_iff] using hqLower
    have hqStable : FiniteSign.Stable
        (FiniteSign.ofRat (q.eval interval.lower))
        (FiniteSign.ofRat (q.eval interval.upper)) :=
      finiteSign_stable_of_eq_zero_or_mul_pos (Or.inr hqEndpoints)
    have hqSignEq : FiniteSign.ofRat (q.eval interval.lower) =
        FiniteSign.ofRat (q.eval interval.upper) := by
      rcases hqStable with hzero | heq
      · exact (hqSign hzero).elim
      · exact heq
    let next := -((divMod p q).remainder)
    have restBounds : FTA.SturmTransducer.NeutralChainResolutionBounds
        interval q (signedRemainderChain q next).tail := by
      simpa only [next] using boundsFromSecond.dropHead
    let restResult :=
      FTA.SturmTransducer.neutralSignedRemainderChainCertificates?_succeeds_of_resolutionBounds
        interval proper q next restBounds hqResolved
    have hcondition : ¬(R.isZero || S.isZero) := by simp [hR, hS]
    have hindex : cauchyIndex2 R S interval.lower interval.upper =
        (signJump (p.eval interval.lower) (q.eval interval.lower) : ℤ) -
          signJump (p.eval interval.upper) (q.eval interval.upper) := by
      rw [cauchyIndex2, if_neg hcondition, cauchyChain]
      change (endpointVariation2
          (signedRemainderChain p q) interval.lower : ℤ) -
        endpointVariation2
          (signedRemainderChain p q) interval.upper = _
      rw [endpointVariation2_signedRemainderChain_step hq interval.lower,
        endpointVariation2_signedRemainderChain_step hq interval.upper,
        show -((divMod p q).remainder) = next by rfl,
        restResult.1.endpointVariation_eq]
      omega
    refine
      { numerator := FiniteSign.ofRat (q.eval interval.lower)
        denominator := .zero
        nonzero := Or.inl hqSign
        numeratorSource := Or.inr ⟨by simpa only [q] using hqResolved, rfl⟩
        denominatorSource := Or.inl ⟨rfl, by simpa only [p] using hpResolved⟩
        numeratorLowerStable := Or.inr rfl
        denominatorLowerStable := Or.inl rfl
        numeratorUpperStable := hqStable
        denominatorUpperStable := Or.inl rfl
        index := ?_ }
    rw [hindex, ← FiniteSign.jump_ofRat, ← FiniteSign.jump_ofRat,
      ← hqSignEq]
    exact (FiniteSign.eventIndex2_of_stableNumerator
      (FiniteSign.ofRat (q.eval interval.lower))
      (FiniteSign.ofRat (p.eval interval.lower))
      (FiniteSign.ofRat (p.eval interval.upper)) hqSign).symm

/-- One positive coefficient-computed width covering the three complete
Cauchy chains of a product cell. -/
def neutralProductChainWidthResolution
    (A B C D : RatPolynomial)
    (hA : A.isZero = false) (hB : B.isZero = false)
    (hC : C.isZero = false) (hD : D.isZero = false)
    (hE : (productNumerator A B C D).isZero = false)
    (hH : (productDenominator A B C D).isZero = false)
    (root : FTA.SturmTransducer.RationalInterval) : ℚ :=
  min
    (FTA.SturmTransducer.cauchyChainAmbientWidthResolution A B hA hB root)
    (min
      (FTA.SturmTransducer.cauchyChainAmbientWidthResolution C D hC hD root)
      (FTA.SturmTransducer.cauchyChainAmbientWidthResolution
        (productNumerator A B C D) (productDenominator A B C D)
        hE hH root))

theorem neutralProductChainWidthResolution_pos
    (A B C D : RatPolynomial)
    (hA : A.isZero = false) (hB : B.isZero = false)
    (hC : C.isZero = false) (hD : D.isZero = false)
    (hE : (productNumerator A B C D).isZero = false)
    (hH : (productDenominator A B C D).isZero = false)
    (root : FTA.SturmTransducer.RationalInterval) :
    0 < neutralProductChainWidthResolution A B C D
      hA hB hC hD hE hH root := by
  apply lt_min
  · exact FTA.SturmTransducer.cauchyChainAmbientWidthResolution_pos
      A B hA hB root
  · apply lt_min
    · exact FTA.SturmTransducer.cauchyChainAmbientWidthResolution_pos
        C D hC hD root
    · exact FTA.SturmTransducer.cauchyChainAmbientWidthResolution_pos
        (productNumerator A B C D) (productDenominator A B C D)
        hE hH root

/-- On the all-resolved branch, the computed three-chain width drives the
actual neutral scanners and returns an exact successful product-leaf result.
This is the coefficient-bounded no-event branch of the eventual total local
classifier resolution. -/
def localProductLeaf?_succeeds_of_neutral_refined_width
    (A B C D : RatPolynomial)
    (hApoly : A.isZero = false) (hBpoly : B.isZero = false)
    (hCpoly : C.isZero = false) (hDpoly : D.isZero = false)
    (hEpoly : (productNumerator A B C D).isZero = false)
    (hHpoly : (productDenominator A B C D).isZero = false)
    (root interval : FTA.SturmTransducer.RationalInterval)
    (hrefines : interval.Refines root) (proper : interval.Proper)
    (hwidth : interval.width < neutralProductChainWidthResolution
      A B C D hApoly hBpoly hCpoly hDpoly hEpoly hHpoly root)
    (hleftHead : FTA.SturmTransducer.MidpointResolved interval
      (reducedDenominator A B))
    (hrightHead : FTA.SturmTransducer.MidpointResolved interval
      (reducedDenominator C D))
    (hproductHead : FTA.SturmTransducer.MidpointResolved interval
      (reducedDenominator (productNumerator A B C D)
        (productDenominator A B C D)))
    (hA : FTA.SturmTransducer.MidpointResolved interval A)
    (hB : FTA.SturmTransducer.MidpointResolved interval B)
    (hC : FTA.SturmTransducer.MidpointResolved interval C)
    (hD : FTA.SturmTransducer.MidpointResolved interval D)
    (hE : FTA.SturmTransducer.MidpointResolved interval
      (productNumerator A B C D))
    (hH : FTA.SturmTransducer.MidpointResolved interval
      (productDenominator A B C D)) :
    { partition : AuxiliaryProductPartition A B C D
        interval.lower interval.upper //
      localProductLeaf? A B C D interval.lower interval.upper =
        some partition } := by
  have hleftWidth : interval.width <
      FTA.SturmTransducer.cauchyChainAmbientWidthResolution
        A B hApoly hBpoly root :=
    hwidth.trans_le (by
      dsimp only [neutralProductChainWidthResolution]
      exact min_le_left _ _)
  have hrightWidth : interval.width <
      FTA.SturmTransducer.cauchyChainAmbientWidthResolution
        C D hCpoly hDpoly root :=
    hwidth.trans_le (by
      dsimp only [neutralProductChainWidthResolution]
      exact (min_le_right _ _).trans (min_le_left _ _))
  have hproductWidth : interval.width <
      FTA.SturmTransducer.cauchyChainAmbientWidthResolution
        (productNumerator A B C D) (productDenominator A B C D)
        hEpoly hHpoly root :=
    hwidth.trans_le (by
      dsimp only [neutralProductChainWidthResolution]
      exact (min_le_right _ _).trans (min_le_right _ _))
  let leftResult :=
    FTA.SturmTransducer.neutralCauchyChainCertificates?_succeeds_of_refined_width
      A B hApoly hBpoly root interval hrefines proper hleftWidth hleftHead
  let rightResult :=
    FTA.SturmTransducer.neutralCauchyChainCertificates?_succeeds_of_refined_width
      C D hCpoly hDpoly root interval hrefines proper hrightWidth hrightHead
  let productResult :=
    FTA.SturmTransducer.neutralCauchyChainCertificates?_succeeds_of_refined_width
      (productNumerator A B C D) (productDenominator A B C D)
      hEpoly hHpoly root interval hrefines proper hproductWidth hproductHead
  have hsome := localProductLeaf?_isSome_of_neutralChains proper
    leftResult.1 rightResult.1 productResult.1 hA hB hC hD hE hH
  cases hleaf : localProductLeaf? A B C D interval.lower interval.upper with
  | none => simp [hleaf] at hsome
  | some partition => exact ⟨partition, rfl⟩

/-- Product of all nonzero members of a finite dense-polynomial list.  Zero
polynomials are deliberately skipped so degenerate coordinates cannot make a
safe-cut guard vanish identically. -/
def nonzeroPolynomialProduct : List RatPolynomial → RatPolynomial
  | [] => constant 1
  | p :: ps =>
      if p.isZero then nonzeroPolynomialProduct ps
      else p * nonzeroPolynomialProduct ps

theorem nonzeroPolynomialProduct_isZero_false (ps : List RatPolynomial) :
    (nonzeroPolynomialProduct ps).isZero = false := by
  induction ps with
  | nil => rfl
  | cons p ps ih =>
      rw [nonzeroPolynomialProduct]
      split
      · exact ih
      · rename_i hp
        apply isZero_mul_eq_false
        · simpa using hp
        · exact ih

/-- A nonzero evaluation of the product that skips identically zero members
forces every displayed nonzero member to be nonzero at that point. -/
theorem eval_ne_zero_of_mem_nonzeroPolynomialProduct
    {ps : List RatPolynomial} {p : RatPolynomial} {x : ℚ}
    (hp : p ∈ ps) (hpNonzero : p.isZero = false)
    (hproduct : (nonzeroPolynomialProduct ps).eval x ≠ 0) :
    p.eval x ≠ 0 := by
  induction ps with
  | nil => simp at hp
  | cons q qs ih =>
      rw [nonzeroPolynomialProduct] at hproduct
      split at hproduct
      · rename_i hqZero
        rcases List.mem_cons.mp hp with rfl | hpTail
        · simp [hpNonzero] at hqZero
        · exact ih hpTail hproduct
      · rename_i hqNonzero
        have hqEval : q.eval x ≠ 0 := by
          intro hzero
          apply hproduct
          simp [hzero]
        have htailEval : (nonzeroPolynomialProduct qs).eval x ≠ 0 := by
          intro hzero
          apply hproduct
          simp [hzero]
        rcases List.mem_cons.mp hp with rfl | hpTail
        · exact hqEval
        · exact ih hpTail htailEval

/-- Every coordinate polynomial and every member of the three executable
Cauchy chains whose signs can affect a local product cell. -/
def productEventPolynomials
    (A B C D : RatPolynomial) : List RatPolynomial :=
  [A, B, C, D, productNumerator A B C D,
    productDenominator A B C D] ++
  cauchyChain A B ++ cauchyChain C D ++
  cauchyChain (productNumerator A B C D)
    (productDenominator A B C D)

/-- Single nonzero guard for all simultaneous product events. -/
def productEventGuard
    (A B C D : RatPolynomial) : RatPolynomial :=
  nonzeroPolynomialProduct (productEventPolynomials A B C D)

theorem productEventGuard_isZero_false (A B C D : RatPolynomial) :
    (productEventGuard A B C D).isZero = false :=
  nonzeroPolynomialProduct_isZero_false _

/-- Extract pointwise clearness of any nonzero event polynomial from the
single executable product guard. -/
theorem productEventPolynomial_eval_ne_zero
    {A B C D p : RatPolynomial} {x : ℚ}
    (hp : p ∈ productEventPolynomials A B C D)
    (hpNonzero : p.isZero = false)
    (hguard : (productEventGuard A B C D).eval x ≠ 0) :
    p.eval x ≠ 0 :=
  eval_ne_zero_of_mem_nonzeroPolynomialProduct hp hpNonzero hguard

/-- Bounded central-third search for a rational cut avoiding every nonzero
coordinate and signed-chain member at once. -/
def productEventCut?
    (A B C D : RatPolynomial) (a b : ℚ) : Option ℚ :=
  FTA.SafeCandidates.centralSearch (productEventGuard A B C D) a b
    (productEventGuard A B C D).natDegree

/-- Total executable cut, with an unreachable midpoint fallback on proper
intervals. -/
def productEventCut
    (A B C D : RatPolynomial) (a b : ℚ) : ℚ :=
  (productEventCut? A B C D a b).getD ((a + b) / 2)

theorem productEventCut_search_succeeds
    (A B C D : RatPolynomial) {a b : ℚ} (hab : a < b) :
    ∃ c, productEventCut? A B C D a b = some c := by
  apply FTA.SafeCandidates.centralSearch_succeeds
    (productEventGuard A B C D) (productEventGuard A B C D).natDegree hab
    (toPolynomial_ne_zero_of_isZero_false
      (productEventGuard_isZero_false A B C D))
  rw [natDegree_toPolynomial (productEventGuard_isZero_false A B C D)]

theorem productEventCut_spec
    (A B C D : RatPolynomial) {a b : ℚ} (hab : a < b) :
    (productEventGuard A B C D).eval (productEventCut A B C D a b) ≠ 0 ∧
      FTA.SafeCandidates.centralLeft a b < productEventCut A B C D a b ∧
      productEventCut A B C D a b < FTA.SafeCandidates.centralRight a b := by
  rcases productEventCut_search_succeeds A B C D hab with ⟨c, hc⟩
  rcases FTA.SafeCandidates.centralSearch_some_spec hab hc with
    ⟨-, hguard, hleft, hright⟩
  have hcut : productEventCut A B C D a b = c := by
    simp [productEventCut, hc]
  rw [hcut]
  exact ⟨hguard, hleft, hright⟩

/-- A safe product-event cut lies strictly inside the parent and contracts
both child widths by the central-third factor. -/
theorem productEventCut_geometry
    (A B C D : RatPolynomial) {a b : ℚ} (hab : a < b) :
    a < productEventCut A B C D a b ∧
    productEventCut A B C D a b < b ∧
    productEventCut A B C D a b - a < (2 / 3 : ℚ) * (b - a) ∧
    b - productEventCut A B C D a b < (2 / 3 : ℚ) * (b - a) := by
  have hspec := productEventCut_spec A B C D hab
  rcases hspec with ⟨-, hleft, hright⟩
  dsimp [FTA.SafeCandidates.centralLeft,
    FTA.SafeCandidates.centralRight] at hleft hright
  constructor
  · linarith
  constructor
  · linarith
  constructor <;> linarith

/-- Fuel-recursive simultaneous product-event partition builder.  A node is
accepted as soon as its executable leaf classifier succeeds; otherwise one
safe central-third cut is consumed and both children are built. -/
def buildAuxiliaryProductPartition?
    (A B C D : RatPolynomial) :
    (fuel : ℕ) → (a b : ℚ) →
      Option (AuxiliaryProductPartition A B C D a b)
  | 0, a, b => localProductLeaf? A B C D a b
  | fuel + 1, a, b =>
      match localProductLeaf? A B C D a b with
      | some partition => some partition
      | none =>
          let cut := productEventCut A B C D a b
          match buildAuxiliaryProductPartition? A B C D fuel a cut with
          | none => none
          | some left =>
              match buildAuxiliaryProductPartition? A B C D fuel cut b with
              | none => none
              | some right => some (.split left right)

/-- Every returned recursive partition proves the auxiliary product formula. -/
theorem buildAuxiliaryProductPartition?_some_auxiliaryProductFormula
    {A B C D : RatPolynomial} {fuel : ℕ} {a b : ℚ}
    {partition : AuxiliaryProductPartition A B C D a b}
    (_hbuild : buildAuxiliaryProductPartition? A B C D fuel a b =
      some partition) :
    AuxiliaryProductFormula A B C D a b :=
  partition.auxiliaryProductFormula

/-- Local-completeness datum for the product-event classifier.  Every proper
subinterval of the root below the displayed positive width is accepted by the
genuine executable leaf classifier. -/
structure ProductEventClassifierResolution
    (A B C D : RatPolynomial) (rootLower rootUpper : ℚ) where
  threshold : ℚ
  positive : 0 < threshold
  classify : ∀ (a b : ℚ), rootLower ≤ a → b ≤ rootUpper → a < b →
    b - a < threshold →
      { partition : AuxiliaryProductPartition A B C D a b //
        localProductLeaf? A B C D a b = some partition }

/-- Operational local-completeness datum for the actual recursive builder.
Every strict subinterval inherits each endpoint either from the ambient root
or from a cut certified nonzero by the common product-event guard. -/
structure GuardedProductEventClassifierResolution
    (A B C D : RatPolynomial) (rootLower rootUpper : ℚ) where
  threshold : ℚ
  positive : 0 < threshold
  classify : ∀ (a b : ℚ), rootLower ≤ a → b ≤ rootUpper → a < b →
    b - a < threshold →
    (a = rootLower ∨ (productEventGuard A B C D).eval a ≠ 0) →
    (b = rootUpper ∨ (productEventGuard A B C D).eval b ≠ 0) →
    (a ≠ rootLower ∨ b ≠ rootUpper) →
      { partition : AuxiliaryProductPartition A B C D a b //
        localProductLeaf? A B C D a b = some partition }

/-- Guard-aware recursion succeeds on every proper strict refinement.  The
safe cut supplies the missing clear endpoint to both children, while the
central-third geometry contracts their required local width. -/
def buildAuxiliaryProductPartition?_succeeds_of_guarded_resolution
    {A B C D : RatPolynomial} {rootLower rootUpper : ℚ}
    (resolution : GuardedProductEventClassifierResolution
      A B C D rootLower rootUpper)
    (fuel : ℕ) (a b : ℚ)
    (hlower : rootLower ≤ a) (hupper : b ≤ rootUpper) (hab : a < b)
    (hlowerGuard : a = rootLower ∨
      (productEventGuard A B C D).eval a ≠ 0)
    (hupperGuard : b = rootUpper ∨
      (productEventGuard A B C D).eval b ≠ 0)
    (hstrict : a ≠ rootLower ∨ b ≠ rootUpper)
    (hsufficient : (2 / 3 : ℚ) ^ fuel * (b - a) <
      resolution.threshold) :
    { partition : AuxiliaryProductPartition A B C D a b //
      buildAuxiliaryProductPartition? A B C D fuel a b =
        some partition } := by
  induction fuel generalizing a b with
  | zero =>
      have hwidth : b - a < resolution.threshold := by
        simpa using hsufficient
      rcases resolution.classify a b hlower hupper hab hwidth
          hlowerGuard hupperGuard hstrict with ⟨partition, hleaf⟩
      exact ⟨partition, by
        change localProductLeaf? A B C D a b = some partition
        exact hleaf⟩
  | succ fuel ih =>
      cases hleaf : localProductLeaf? A B C D a b with
      | some partition =>
          refine ⟨partition, ?_⟩
          rw [buildAuxiliaryProductPartition?, hleaf]
      | none =>
          let cut := productEventCut A B C D a b
          have hcutGuard : (productEventGuard A B C D).eval cut ≠ 0 := by
            exact (productEventCut_spec A B C D hab).1
          have hgeometry := productEventCut_geometry A B C D hab
          have hleftProper : a < cut := hgeometry.1
          have hrightProper : cut < b := hgeometry.2.1
          have hleftWidth : cut - a < (2 / 3 : ℚ) * (b - a) :=
            hgeometry.2.2.1
          have hrightWidth : b - cut < (2 / 3 : ℚ) * (b - a) :=
            hgeometry.2.2.2
          have hfactor : 0 < (2 / 3 : ℚ) ^ fuel := by positivity
          have hleftSufficient : (2 / 3 : ℚ) ^ fuel * (cut - a) <
              resolution.threshold := by
            calc
              (2 / 3 : ℚ) ^ fuel * (cut - a) <
                  (2 / 3 : ℚ) ^ fuel * ((2 / 3 : ℚ) * (b - a)) :=
                mul_lt_mul_of_pos_left hleftWidth hfactor
              _ = (2 / 3 : ℚ) ^ (fuel + 1) * (b - a) := by
                rw [pow_succ]
                ring
              _ < resolution.threshold := by
                simpa [Nat.succ_eq_add_one] using hsufficient
          have hrightSufficient : (2 / 3 : ℚ) ^ fuel * (b - cut) <
              resolution.threshold := by
            calc
              (2 / 3 : ℚ) ^ fuel * (b - cut) <
                  (2 / 3 : ℚ) ^ fuel * ((2 / 3 : ℚ) * (b - a)) :=
                mul_lt_mul_of_pos_left hrightWidth hfactor
              _ = (2 / 3 : ℚ) ^ (fuel + 1) * (b - a) := by
                rw [pow_succ]
                ring
              _ < resolution.threshold := by
                simpa [Nat.succ_eq_add_one] using hsufficient
          have hcutLower : rootLower ≤ cut :=
            hlower.trans hleftProper.le
          have hcutUpper : cut ≤ rootUpper :=
            hrightProper.le.trans hupper
          have hleftStrict : a ≠ rootLower ∨ cut ≠ rootUpper :=
            Or.inr (hrightProper.trans_le hupper).ne
          have hrightStrict : cut ≠ rootLower ∨ b ≠ rootUpper :=
            Or.inl (hlower.trans_lt hleftProper).ne'
          have leftResult := ih a cut hlower hcutUpper hleftProper
            hlowerGuard (Or.inr hcutGuard) hleftStrict hleftSufficient
          have rightResult := ih cut b hcutLower hupper hrightProper
            (Or.inr hcutGuard) hupperGuard hrightStrict hrightSufficient
          dsimp only [cut] at leftResult rightResult
          refine ⟨.split leftResult.1 rightResult.1, ?_⟩
          rw [buildAuxiliaryProductPartition?, hleaf]
          dsimp only
          simp only [leftResult.2, rightResult.2]

/-- Starting from the ambient root itself needs one initial cut before the
strict-refinement invariant is available.  If the root leaf already works it
is returned immediately; otherwise both children satisfy the guard-aware
recursive theorem. -/
def buildAuxiliaryProductPartition?_succeeds_at_root_of_guarded_resolution
    {A B C D : RatPolynomial} {rootLower rootUpper : ℚ}
    (resolution : GuardedProductEventClassifierResolution
      A B C D rootLower rootUpper)
    (fuel : ℕ) (hroot : rootLower < rootUpper)
    (hsufficient : (2 / 3 : ℚ) ^ (fuel + 1) *
      (rootUpper - rootLower) < resolution.threshold) :
    { partition : AuxiliaryProductPartition A B C D rootLower rootUpper //
      buildAuxiliaryProductPartition? A B C D (fuel + 1)
        rootLower rootUpper = some partition } := by
  cases hleaf : localProductLeaf? A B C D rootLower rootUpper with
  | some partition =>
      refine ⟨partition, ?_⟩
      rw [buildAuxiliaryProductPartition?, hleaf]
  | none =>
      let cut := productEventCut A B C D rootLower rootUpper
      have hcutGuard : (productEventGuard A B C D).eval cut ≠ 0 :=
        (productEventCut_spec A B C D hroot).1
      have hgeometry := productEventCut_geometry A B C D hroot
      have hleftProper : rootLower < cut := hgeometry.1
      have hrightProper : cut < rootUpper := hgeometry.2.1
      have hleftWidth : cut - rootLower <
          (2 / 3 : ℚ) * (rootUpper - rootLower) := hgeometry.2.2.1
      have hrightWidth : rootUpper - cut <
          (2 / 3 : ℚ) * (rootUpper - rootLower) := hgeometry.2.2.2
      have hfactor : 0 < (2 / 3 : ℚ) ^ fuel := by positivity
      have hleftSufficient : (2 / 3 : ℚ) ^ fuel *
          (cut - rootLower) < resolution.threshold := by
        calc
          (2 / 3 : ℚ) ^ fuel * (cut - rootLower) <
              (2 / 3 : ℚ) ^ fuel *
                ((2 / 3 : ℚ) * (rootUpper - rootLower)) :=
            mul_lt_mul_of_pos_left hleftWidth hfactor
          _ = (2 / 3 : ℚ) ^ (fuel + 1) *
              (rootUpper - rootLower) := by
            rw [pow_succ]
            ring
          _ < resolution.threshold := hsufficient
      have hrightSufficient : (2 / 3 : ℚ) ^ fuel *
          (rootUpper - cut) < resolution.threshold := by
        calc
          (2 / 3 : ℚ) ^ fuel * (rootUpper - cut) <
              (2 / 3 : ℚ) ^ fuel *
                ((2 / 3 : ℚ) * (rootUpper - rootLower)) :=
            mul_lt_mul_of_pos_left hrightWidth hfactor
          _ = (2 / 3 : ℚ) ^ (fuel + 1) *
              (rootUpper - rootLower) := by
            rw [pow_succ]
            ring
          _ < resolution.threshold := hsufficient
      have leftResult :=
        buildAuxiliaryProductPartition?_succeeds_of_guarded_resolution
          resolution fuel rootLower cut le_rfl hrightProper.le hleftProper
          (Or.inl rfl) (Or.inr hcutGuard)
          (Or.inr hrightProper.ne) hleftSufficient
      have rightResult :=
        buildAuxiliaryProductPartition?_succeeds_of_guarded_resolution
          resolution fuel cut rootUpper hleftProper.le le_rfl hrightProper
          (Or.inr hcutGuard) (Or.inl rfl)
          (Or.inl hleftProper.ne') hrightSufficient
      dsimp only [cut] at leftResult rightResult
      refine ⟨.split leftResult.1 rightResult.1, ?_⟩
      rw [buildAuxiliaryProductPartition?, hleaf]
      dsimp only
      simp only [leftResult.2, rightResult.2]

/-- Explicit natural depth for a guard-aware product-event resolution. -/
def guardedProductEventResolutionDepth
    {A B C D : RatPolynomial} {rootLower rootUpper : ℚ}
    (resolution : GuardedProductEventClassifierResolution
      A B C D rootLower rootUpper) : ℕ :=
  FTA.SturmTransducer.geometricDepth (rootUpper - rootLower)
    (resolution.threshold / 2)

theorem guardedProductEventResolutionDepth_sufficient
    {A B C D : RatPolynomial} {rootLower rootUpper : ℚ}
    (hroot : rootLower < rootUpper)
    (resolution : GuardedProductEventClassifierResolution
      A B C D rootLower rootUpper) :
    (2 / 3 : ℚ) ^ (guardedProductEventResolutionDepth resolution + 1) *
        (rootUpper - rootLower) < resolution.threshold := by
  let depth := guardedProductEventResolutionDepth resolution
  have hhalf : 0 < resolution.threshold / 2 := by
    linarith [resolution.positive]
  have hgeometric := FTA.SturmTransducer.geometricDepth_sufficient
    (sub_nonneg.mpr hroot.le) hhalf
  have hbase : (2 / 3 : ℚ) ^ depth * (rootUpper - rootLower) ≤
      resolution.threshold / 2 := by
    simpa [depth, guardedProductEventResolutionDepth] using hgeometric
  have hbaseNonneg : 0 ≤
      (2 / 3 : ℚ) ^ depth * (rootUpper - rootLower) :=
    mul_nonneg (by positivity) (sub_nonneg.mpr hroot.le)
  calc
    (2 / 3 : ℚ) ^ (guardedProductEventResolutionDepth resolution + 1) *
        (rootUpper - rootLower) =
      (2 / 3 : ℚ) *
        ((2 / 3 : ℚ) ^ depth * (rootUpper - rootLower)) := by
          dsimp only [depth]
          rw [pow_succ]
          ring
    _ ≤ (2 / 3 : ℚ) ^ depth * (rootUpper - rootLower) := by
      linarith
    _ ≤ resolution.threshold / 2 := hbase
    _ < resolution.threshold := by linarith [resolution.positive]

/-- A displayed local resolution and a displayed geometric depth make the
safe-cut recursive product partition builder constructively successful. -/
def buildAuxiliaryProductPartition?_succeeds_of_resolution
    {A B C D : RatPolynomial} {rootLower rootUpper : ℚ}
    (resolution : ProductEventClassifierResolution
      A B C D rootLower rootUpper)
    (fuel : ℕ) (a b : ℚ)
    (hlower : rootLower ≤ a) (hupper : b ≤ rootUpper) (hab : a < b)
    (hsufficient : (2 / 3 : ℚ) ^ fuel * (b - a) <
      resolution.threshold) :
    { partition : AuxiliaryProductPartition A B C D a b //
      buildAuxiliaryProductPartition? A B C D fuel a b =
        some partition } := by
  induction fuel generalizing a b with
  | zero =>
      have hwidth : b - a < resolution.threshold := by
        simpa using hsufficient
      rcases resolution.classify a b hlower hupper hab hwidth with
        ⟨partition, hleaf⟩
      refine ⟨partition, ?_⟩
      change localProductLeaf? A B C D a b = some partition
      exact hleaf
  | succ fuel ih =>
      cases hleaf : localProductLeaf? A B C D a b with
      | some partition =>
          refine ⟨partition, ?_⟩
          rw [buildAuxiliaryProductPartition?]
          rw [hleaf]
      | none =>
          let cut := productEventCut A B C D a b
          have hgeometry := productEventCut_geometry A B C D hab
          have hleftProper : a < cut := hgeometry.1
          have hrightProper : cut < b := hgeometry.2.1
          have hleftWidth : cut - a < (2 / 3 : ℚ) * (b - a) :=
            hgeometry.2.2.1
          have hrightWidth : b - cut < (2 / 3 : ℚ) * (b - a) :=
            hgeometry.2.2.2
          have hfactor : 0 < (2 / 3 : ℚ) ^ fuel := by positivity
          have hleftSufficient : (2 / 3 : ℚ) ^ fuel * (cut - a) <
              resolution.threshold := by
            calc
              (2 / 3 : ℚ) ^ fuel * (cut - a) <
                  (2 / 3 : ℚ) ^ fuel *
                    ((2 / 3 : ℚ) * (b - a)) :=
                mul_lt_mul_of_pos_left hleftWidth hfactor
              _ = (2 / 3 : ℚ) ^ (fuel + 1) * (b - a) := by
                rw [pow_succ]
                ring
              _ < resolution.threshold := by
                simpa [Nat.succ_eq_add_one] using hsufficient
          have hrightSufficient : (2 / 3 : ℚ) ^ fuel * (b - cut) <
              resolution.threshold := by
            calc
              (2 / 3 : ℚ) ^ fuel * (b - cut) <
                  (2 / 3 : ℚ) ^ fuel *
                    ((2 / 3 : ℚ) * (b - a)) :=
                mul_lt_mul_of_pos_left hrightWidth hfactor
              _ = (2 / 3 : ℚ) ^ (fuel + 1) * (b - a) := by
                rw [pow_succ]
                ring
              _ < resolution.threshold := by
                simpa [Nat.succ_eq_add_one] using hsufficient
          have hcutLower : rootLower ≤ cut := le_trans hlower hleftProper.le
          have hcutUpper : cut ≤ rootUpper := le_trans hrightProper.le hupper
          have leftResult := ih a cut hlower hcutUpper hleftProper
            hleftSufficient
          have rightResult := ih cut b hcutLower hupper hrightProper
            hrightSufficient
          dsimp only [cut] at leftResult rightResult
          refine ⟨.split leftResult.1 rightResult.1, ?_⟩
          rw [buildAuxiliaryProductPartition?]
          rw [hleaf]
          dsimp only
          simp only [leftResult.2, rightResult.2]

/-- Explicit conservative central-third depth for one product-event
resolution, obtained from rational ceiling arithmetic rather than logarithms. -/
def productEventResolutionDepth
    {A B C D : RatPolynomial} {rootLower rootUpper : ℚ}
    (resolution : ProductEventClassifierResolution
      A B C D rootLower rootUpper) : ℕ :=
  FTA.SturmTransducer.geometricDepth (rootUpper - rootLower)
    (resolution.threshold / 2)

theorem productEventResolutionDepth_sufficient
    {A B C D : RatPolynomial} {rootLower rootUpper : ℚ}
    (hroot : rootLower < rootUpper)
    (resolution : ProductEventClassifierResolution
      A B C D rootLower rootUpper) :
    (2 / 3 : ℚ) ^ productEventResolutionDepth resolution *
        (rootUpper - rootLower) < resolution.threshold := by
  have hhalf : 0 < resolution.threshold / 2 := by
    linarith [resolution.positive]
  have hgeometric := FTA.SturmTransducer.geometricDepth_sufficient
    (show 0 ≤ rootUpper - rootLower by linarith) hhalf
  calc
    (2 / 3 : ℚ) ^ productEventResolutionDepth resolution *
        (rootUpper - rootLower) ≤ resolution.threshold / 2 := by
      simpa [productEventResolutionDepth] using hgeometric
    _ < resolution.threshold := by linarith [resolution.positive]

/-- Uniform provider for root-interval-dependent local product-event
resolution data. -/
structure ProductEventClassifierResolutionProgram
    (A B C D : RatPolynomial) where
  resolve : ∀ (a b : ℚ), a < b →
    ProductEventClassifierResolution A B C D a b

/-- Constructive product-partition interface produced by the finite builder. -/
structure AuxiliaryProductPartitionProgram
    (A B C D : RatPolynomial) where
  run : ∀ (a b : ℚ), a < b → AuxiliaryProductPartition A B C D a b

/-- A uniform local-resolution program plus the explicit geometric depth
produces a total finite product-partition program. -/
def ProductEventClassifierResolutionProgram.toPartitionProgram
    {A B C D : RatPolynomial}
    (resolutions : ProductEventClassifierResolutionProgram A B C D) :
    AuxiliaryProductPartitionProgram A B C D where
  run := by
    intro a b hab
    let resolution := resolutions.resolve a b hab
    let depth := productEventResolutionDepth resolution
    have hsufficient : (2 / 3 : ℚ) ^ depth * (b - a) <
        resolution.threshold := by
      simpa [resolution, depth] using
        productEventResolutionDepth_sufficient hab resolution
    exact (buildAuxiliaryProductPartition?_succeeds_of_resolution
      resolution depth a b le_rfl le_rfl hab hsufficient).1

/-- Every total partition program supplies the universal auxiliary product
formula on proper rational intervals. -/
theorem AuxiliaryProductPartitionProgram.auxiliaryProductFormula
    {A B C D : RatPolynomial}
    (program : AuxiliaryProductPartitionProgram A B C D)
    {a b : ℚ} (hab : a < b) :
    AuxiliaryProductFormula A B C D a b :=
  (program.run a b hab).auxiliaryProductFormula

/-! ## Uniqueness of coprime fraction representatives -/

/-- Two nonzero coprime polynomial pairs representing the same rational
function differ by one nonzero scalar.  This is the algebraic cancellation
lemma needed to compare independently gcd-reduced coordinate pairs. -/
theorem coprimePolynomialPairs_eq_scalar
    {p q r s : Polynomial ℚ}
    (hpq : IsCoprime p q) (hrs : IsCoprime r s)
    (hp : p ≠ 0) (hq : q ≠ 0)
    (hcross : p * s = r * q) :
    ∃ c : ℚ, c ≠ 0 ∧ r = Polynomial.C c * p ∧
      s = Polynomial.C c * q := by
  have hpDividesR : p ∣ r := by
    apply hpq.dvd_of_dvd_mul_left
    refine ⟨s, ?_⟩
    simpa [mul_comm] using hcross.symm
  have hqDividesS : q ∣ s := by
    apply hpq.symm.dvd_of_dvd_mul_left
    refine ⟨r, ?_⟩
    simpa [mul_comm] using hcross
  rcases hpDividesR with ⟨k, hk⟩
  rcases hqDividesS with ⟨l, hl⟩
  have hkl : l = k := by
    apply mul_left_cancel₀ (mul_ne_zero hp hq)
    calc
      p * q * l = p * (q * l) := by ring
      _ = p * s := by rw [hl]
      _ = r * q := hcross
      _ = (p * k) * q := by rw [hk]
      _ = p * q * k := by ring
  subst l
  have hkDividesR : k ∣ r := ⟨p, by simpa [mul_comm] using hk⟩
  have hkDividesS : k ∣ s := ⟨q, by simpa [mul_comm] using hl⟩
  have hkUnit : IsUnit k := hrs.isUnit_of_dvd' hkDividesR hkDividesS
  let c := k.coeff 0
  have hkDegree : k.degree = 0 := Polynomial.degree_eq_zero_of_isUnit hkUnit
  have hkDegreeLe : k.degree ≤ 0 := hkDegree.le
  have hkConstant : k = Polynomial.C c := by
    simpa only [c] using Polynomial.eq_C_of_degree_le_zero hkDegreeLe
  have hc : c ≠ 0 := by
    intro hc
    have hkZero : k = 0 := by simp [hkConstant, hc]
    rw [hkZero] at hkUnit
    exact not_isUnit_zero hkUnit
  refine ⟨c, hc, ?_, ?_⟩
  · rw [hk, hkConstant]
    ring
  · rw [hl, hkConstant]
    ring

/-- The gcd-reduced numerator and denominator represent the same rational
function as the original dense pair. -/
theorem reducedPair_cross_identity (R S : RatPolynomial) :
    R.toPolynomial * (reducedDenominator R S).toPolynomial =
      S.toPolynomial * (reducedNumerator R S).toPolynomial := by
  unfold reducedNumerator reducedDenominator
  calc
    R.toPolynomial *
        (FTA.DenseGCD.symmetricRightFactor R S).toPolynomial =
        ((FTA.DenseGCD.symmetricGCD R S).toPolynomial *
          (FTA.DenseGCD.symmetricLeftFactor R S).toPolynomial) *
            (FTA.DenseGCD.symmetricRightFactor R S).toPolynomial := by
      rw [← FTA.DenseGCD.symmetricLeftFactor_toPolynomial_identity R S]
    _ = ((FTA.DenseGCD.symmetricGCD R S).toPolynomial *
          (FTA.DenseGCD.symmetricRightFactor R S).toPolynomial) *
            (FTA.DenseGCD.symmetricLeftFactor R S).toPolynomial := by ring
    _ = S.toPolynomial *
          (FTA.DenseGCD.symmetricLeftFactor R S).toPolynomial := by
      rw [← FTA.DenseGCD.symmetricRightFactor_toPolynomial_identity R S]

/-- Constructive common scalar relating a coprime input pair to its executable
gcd-reduced representative. -/
structure CoprimePairReductionScale (R S : RatPolynomial) where
  scalar : ℚ
  nonzero : scalar ≠ 0
  numeratorEval : ∀ x : ℚ,
    R.eval x = scalar * (reducedNumerator R S).eval x
  denominatorEval : ∀ x : ℚ,
    S.eval x = scalar * (reducedDenominator R S).eval x

/-- The scalar is computed from the constant symmetric gcd.  Returning a
proof-relevant structure keeps the lift executable rather than choosing from
a propositional existence theorem. -/
def coprimePairReductionScale
    (R S : RatPolynomial)
    (coprime : FTA.DenseSquarefree.CoprimeCertificate R S) :
    CoprimePairReductionScale R S := by
  let g := FTA.DenseGCD.symmetricGCD R S
  have hgDividesR : g.toPolynomial ∣ R.toPolynomial :=
    ⟨(reducedNumerator R S).toPolynomial, by
      simpa only [g, reducedNumerator] using
        FTA.DenseGCD.symmetricLeftFactor_toPolynomial_identity R S⟩
  have hgDividesS : g.toPolynomial ∣ S.toPolynomial :=
    ⟨(reducedDenominator R S).toPolynomial, by
      simpa only [g, reducedDenominator] using
        FTA.DenseGCD.symmetricRightFactor_toPolynomial_identity R S⟩
  have hgUnit : IsUnit g.toPolynomial :=
    coprime.isCoprime.isUnit_of_dvd' hgDividesR hgDividesS
  let c := g.eval 0
  have hgDegree : g.toPolynomial.degree = 0 :=
    Polynomial.degree_eq_zero_of_isUnit hgUnit
  have hcoeff : g.toPolynomial.coeff 0 = c := by
    rw [Polynomial.coeff_zero_eq_eval_zero, eval_toPolynomial]
  have hgConstant : g.toPolynomial = Polynomial.C c := by
    rw [← hcoeff]
    exact Polynomial.eq_C_of_degree_le_zero hgDegree.le
  have hc : c ≠ 0 := by
    intro hc
    have hgZero : g.toPolynomial = 0 := by simp [hgConstant, hc]
    rw [hgZero] at hgUnit
    exact not_isUnit_zero hgUnit
  refine
    { scalar := c
      nonzero := hc
      numeratorEval := ?_
      denominatorEval := ?_ }
  · intro x
    rw [FTA.DenseGCD.symmetricLeftFactor_eval_identity R S x]
    have hgEval : g.eval x = c := by
      rw [← eval_toPolynomial, hgConstant, Polynomial.eval_C]
    simp only [g, c, reducedNumerator, hgEval]
  · intro x
    rw [FTA.DenseGCD.symmetricRightFactor_eval_identity R S x]
    have hgEval : g.eval x = c := by
      rw [← eval_toPolynomial, hgConstant, Polynomial.eval_C]
    simp only [g, c, reducedDenominator, hgEval]

/-- Formal center signs expressed in the original coprime coordinates rather
than in the canonical gcd-reduced representatives. -/
structure CauchyEventSigns
    (R S : RatPolynomial)
    (interval : FTA.SturmTransducer.RationalInterval) where
  numerator : FiniteSign
  denominator : FiniteSign
  nonzero : numerator ≠ .zero ∨ denominator ≠ .zero
  numeratorLowerStable : FiniteSign.Stable numerator
    (FiniteSign.ofRat (R.eval interval.lower))
  denominatorLowerStable : FiniteSign.Stable denominator
    (FiniteSign.ofRat (S.eval interval.lower))
  numeratorUpperStable : FiniteSign.Stable numerator
    (FiniteSign.ofRat (R.eval interval.upper))
  denominatorUpperStable : FiniteSign.Stable denominator
    (FiniteSign.ofRat (S.eval interval.upper))
  index : cauchyIndex2 R S interval.lower interval.upper =
    FiniteSign.eventIndex2 numerator denominator
      (FiniteSign.ofRat (R.eval interval.lower))
      (FiniteSign.ofRat (S.eval interval.lower))
      (FiniteSign.ofRat (R.eval interval.upper))
      (FiniteSign.ofRat (S.eval interval.upper))

namespace CauchyEventSigns

/-- Replace the formal center by any other nonzero pair stable against the
same endpoints.  The finite uniqueness table proves that the represented
Cauchy index is unchanged. -/
def recenter
    {R S : RatPolynomial}
    {interval : FTA.SturmTransducer.RationalInterval}
    (data : CauchyEventSigns R S interval)
    (numerator denominator : FiniteSign)
    (nonzero : numerator ≠ .zero ∨ denominator ≠ .zero)
    (numeratorLowerStable : FiniteSign.Stable numerator
      (FiniteSign.ofRat (R.eval interval.lower)))
    (denominatorLowerStable : FiniteSign.Stable denominator
      (FiniteSign.ofRat (S.eval interval.lower)))
    (numeratorUpperStable : FiniteSign.Stable numerator
      (FiniteSign.ofRat (R.eval interval.upper)))
    (denominatorUpperStable : FiniteSign.Stable denominator
      (FiniteSign.ofRat (S.eval interval.upper))) :
    CauchyEventSigns R S interval where
  numerator := numerator
  denominator := denominator
  nonzero := nonzero
  numeratorLowerStable := numeratorLowerStable
  denominatorLowerStable := denominatorLowerStable
  numeratorUpperStable := numeratorUpperStable
  denominatorUpperStable := denominatorUpperStable
  index := by
    rw [data.index]
    exact FiniteSign.eventIndex2_eq_of_stable
      data.numerator data.denominator numerator denominator
      (FiniteSign.ofRat (R.eval interval.lower))
      (FiniteSign.ofRat (S.eval interval.lower))
      (FiniteSign.ofRat (R.eval interval.upper))
      (FiniteSign.ofRat (S.eval interval.upper))
      ⟨data.nonzero, data.numeratorLowerStable,
        data.denominatorLowerStable, data.numeratorUpperStable,
        data.denominatorUpperStable⟩
      ⟨nonzero, numeratorLowerStable, denominatorLowerStable,
        numeratorUpperStable, denominatorUpperStable⟩

/-- If the exact signs at the left rational endpoint are nonzero as a pair
and remain stable at the right endpoint, a certified two-sided event record
computes exactly the paper's one-sided left-endpoint pole contribution. -/
theorem index_eq_leftEndpointIndex2
    {R S : RatPolynomial}
    {interval : FTA.SturmTransducer.RationalInterval}
    (data : CauchyEventSigns R S interval)
    (hnonzero : R.eval interval.lower ≠ 0 ∨
      S.eval interval.lower ≠ 0)
    (hnumerator : R.eval interval.lower = 0 ∨
      0 < R.eval interval.lower * R.eval interval.upper)
    (hdenominator : S.eval interval.lower = 0 ∨
      0 < S.eval interval.lower * S.eval interval.upper) :
    cauchyIndex2 R S interval.lower interval.upper =
      leftEndpointIndex2
        (R.eval interval.lower) (S.eval interval.lower)
        (R.eval interval.upper) (S.eval interval.upper) := by
  let centered := data.recenter
    (FiniteSign.ofRat (R.eval interval.lower))
    (FiniteSign.ofRat (S.eval interval.lower))
    (by simpa [FiniteSign.ofRat_eq_zero_iff] using hnonzero)
    (Or.inr rfl) (Or.inr rfl)
    (finiteSign_stable_of_eq_zero_or_mul_pos hnumerator)
    (finiteSign_stable_of_eq_zero_or_mul_pos hdenominator)
  have hindex : cauchyIndex2 R S interval.lower interval.upper =
      FiniteSign.eventIndex2
        (FiniteSign.ofRat (R.eval interval.lower))
        (FiniteSign.ofRat (S.eval interval.lower))
        (FiniteSign.ofRat (R.eval interval.lower))
        (FiniteSign.ofRat (S.eval interval.lower))
        (FiniteSign.ofRat (R.eval interval.upper))
        (FiniteSign.ofRat (S.eval interval.upper)) := by
    simpa only [centered, recenter] using centered.index
  rw [hindex, FiniteSign.eventIndex2_self_left,
    finiteSign_leftEndpointIndex2_ofRat]

/-- The symmetric endpoint formula: if the exact right signs are a nonzero
stable pair, the reversed Cauchy index is the right endpoint's one-sided pole
contribution toward the displayed left point. -/
theorem reverse_index_eq_leftEndpointIndex2
    {R S : RatPolynomial}
    {interval : FTA.SturmTransducer.RationalInterval}
    (data : CauchyEventSigns R S interval)
    (hnonzero : R.eval interval.upper ≠ 0 ∨
      S.eval interval.upper ≠ 0)
    (hnumerator : R.eval interval.upper = 0 ∨
      0 < R.eval interval.upper * R.eval interval.lower)
    (hdenominator : S.eval interval.upper = 0 ∨
      0 < S.eval interval.upper * S.eval interval.lower) :
    cauchyIndex2 R S interval.upper interval.lower =
      leftEndpointIndex2
        (R.eval interval.upper) (S.eval interval.upper)
        (R.eval interval.lower) (S.eval interval.lower) := by
  let centered := data.recenter
    (FiniteSign.ofRat (R.eval interval.upper))
    (FiniteSign.ofRat (S.eval interval.upper))
    (by simpa [FiniteSign.ofRat_eq_zero_iff] using hnonzero)
    (finiteSign_stable_of_eq_zero_or_mul_pos hnumerator)
    (finiteSign_stable_of_eq_zero_or_mul_pos hdenominator)
    (Or.inr rfl) (Or.inr rfl)
  have hindex : cauchyIndex2 R S interval.lower interval.upper =
      FiniteSign.eventIndex2
        (FiniteSign.ofRat (R.eval interval.upper))
        (FiniteSign.ofRat (S.eval interval.upper))
        (FiniteSign.ofRat (R.eval interval.lower))
        (FiniteSign.ofRat (S.eval interval.lower))
        (FiniteSign.ofRat (R.eval interval.upper))
        (FiniteSign.ofRat (S.eval interval.upper)) := by
    simpa only [centered, recenter] using centered.index
  rw [cauchyIndex2_reverse, hindex,
    FiniteSign.neg_eventIndex2_self_right,
    finiteSign_leftEndpointIndex2_ofRat]

end CauchyEventSigns

/-- A positive coefficient-computed radius around one fixed rational
endpoint.  If the polynomial already vanishes there, endpoint stability is
automatic; otherwise the radius is its exact value margin divided by a
global Lipschitz majorant on the ambient interval. -/
def endpointStabilityWidth
    (p : RatPolynomial)
    (root : FTA.SturmTransducer.RationalInterval) (x : ℚ) : ℚ :=
  if p.eval x = 0 then 1 else
    |p.eval x| /
      max 1 (denseEvalLipschitzBound p
        (intervalMagnitude root.lower root.upper))

theorem endpointStabilityWidth_pos
    (p : RatPolynomial)
    (root : FTA.SturmTransducer.RationalInterval) (x : ℚ) :
    0 < endpointStabilityWidth p root x := by
  by_cases hx : p.eval x = 0
  · simp [endpointStabilityWidth, hx]
  · rw [endpointStabilityWidth, if_neg hx]
    exact div_pos (abs_pos.mpr hx)
      (lt_of_lt_of_le zero_lt_one (le_max_left _ _))

/-- Two points in the ambient interval that are closer than the endpoint
stability width either start at an exact zero or have the same strict
polynomial sign. -/
theorem eval_eq_zero_or_mul_pos_of_endpointStabilityWidth
    (p : RatPolynomial)
    (root : FTA.SturmTransducer.RationalInterval) {x y : ℚ}
    (hxLower : root.lower ≤ x) (hxUpper : x ≤ root.upper)
    (hyLower : root.lower ≤ y) (hyUpper : y ≤ root.upper)
    (hdistance : |x - y| < endpointStabilityWidth p root x) :
    p.eval x = 0 ∨ 0 < p.eval x * p.eval y := by
  by_cases hx : p.eval x = 0
  · exact Or.inl hx
  · apply Or.inr
    let bound := intervalMagnitude root.lower root.upper
    let majorant := max 1 (denseEvalLipschitzBound p bound)
    have hbound : 0 ≤ bound :=
      (intervalMagnitude_pos root.lower root.upper).le
    have hxBound : |x| ≤ bound :=
      abs_le_intervalMagnitude hxLower hxUpper
    have hyBound : |y| ≤ bound :=
      abs_le_intervalMagnitude hyLower hyUpper
    have hmajorantPos : 0 < majorant :=
      lt_of_lt_of_le zero_lt_one (le_max_left _ _)
    have hscaled : majorant * |x - y| < |p.eval x| := by
      have := (lt_div_iff₀ hmajorantPos).mp
        (by simpa [endpointStabilityWidth, hx, bound, majorant] using hdistance)
      simpa [mul_comm] using this
    have hslopeLe : denseEvalLipschitzBound p bound ≤ majorant :=
      le_max_right _ _
    apply mul_pos_of_abs_sub_lt_abs_left
    exact (abs_dense_eval_sub_eval_le_dense p hbound hxBound hyBound).trans_lt
      (lt_of_le_of_lt
        (mul_le_mul_of_nonneg_right hslopeLe (abs_nonneg _)) hscaled)

/-- One endpoint radius simultaneously stabilizing the two factor pairs and
their two exact product coordinates. -/
def productEndpointStabilityWidth
    (A B C D : RatPolynomial)
    (root : FTA.SturmTransducer.RationalInterval) (x : ℚ) : ℚ :=
  min (endpointStabilityWidth A root x)
    (min (endpointStabilityWidth B root x)
      (min (endpointStabilityWidth C root x)
        (min (endpointStabilityWidth D root x)
          (min
            (endpointStabilityWidth (productNumerator A B C D) root x)
            (endpointStabilityWidth
              (productDenominator A B C D) root x)))))

theorem productEndpointStabilityWidth_pos
    (A B C D : RatPolynomial)
    (root : FTA.SturmTransducer.RationalInterval) (x : ℚ) :
    0 < productEndpointStabilityWidth A B C D root x := by
  dsimp only [productEndpointStabilityWidth]
  apply lt_min
  · exact endpointStabilityWidth_pos A root x
  · apply lt_min
    · exact endpointStabilityWidth_pos B root x
    · apply lt_min
      · exact endpointStabilityWidth_pos C root x
      · apply lt_min
        · exact endpointStabilityWidth_pos D root x
        · apply lt_min
          · exact endpointStabilityWidth_pos
              (productNumerator A B C D) root x
          · exact endpointStabilityWidth_pos
              (productDenominator A B C D) root x

/-- A distance below the simultaneous endpoint radius supplies precisely the
six zero-or-same-sign facts consumed by the executable endpoint table. -/
theorem productEndpointStability_of_distance
    (A B C D : RatPolynomial)
    (root : FTA.SturmTransducer.RationalInterval) {x y : ℚ}
    (hxLower : root.lower ≤ x) (hxUpper : x ≤ root.upper)
    (hyLower : root.lower ≤ y) (hyUpper : y ≤ root.upper)
    (hdistance : |x - y| <
      productEndpointStabilityWidth A B C D root x) :
    (A.eval x = 0 ∨ 0 < A.eval x * A.eval y) ∧
    (B.eval x = 0 ∨ 0 < B.eval x * B.eval y) ∧
    (C.eval x = 0 ∨ 0 < C.eval x * C.eval y) ∧
    (D.eval x = 0 ∨ 0 < D.eval x * D.eval y) ∧
    ((productNumerator A B C D).eval x = 0 ∨
      0 < (productNumerator A B C D).eval x *
        (productNumerator A B C D).eval y) ∧
    ((productDenominator A B C D).eval x = 0 ∨
      0 < (productDenominator A B C D).eval x *
        (productDenominator A B C D).eval y) := by
  have hA : |x - y| < endpointStabilityWidth A root x :=
    hdistance.trans_le (by
      dsimp only [productEndpointStabilityWidth]
      exact min_le_left _ _)
  have hB : |x - y| < endpointStabilityWidth B root x :=
    hdistance.trans_le (by
      dsimp only [productEndpointStabilityWidth]
      exact (min_le_right _ _).trans (min_le_left _ _))
  have hC : |x - y| < endpointStabilityWidth C root x :=
    hdistance.trans_le (by
      dsimp only [productEndpointStabilityWidth]
      exact (min_le_right _ _).trans
        ((min_le_right _ _).trans (min_le_left _ _)))
  have hD : |x - y| < endpointStabilityWidth D root x :=
    hdistance.trans_le (by
      dsimp only [productEndpointStabilityWidth]
      exact (min_le_right _ _).trans
        ((min_le_right _ _).trans
          ((min_le_right _ _).trans (min_le_left _ _))))
  have hE : |x - y| < endpointStabilityWidth
      (productNumerator A B C D) root x :=
    hdistance.trans_le (by
      dsimp only [productEndpointStabilityWidth]
      exact (min_le_right _ _).trans
        ((min_le_right _ _).trans
          ((min_le_right _ _).trans
            ((min_le_right _ _).trans (min_le_left _ _)))))
  have hH : |x - y| < endpointStabilityWidth
      (productDenominator A B C D) root x :=
    hdistance.trans_le (by
      dsimp only [productEndpointStabilityWidth]
      exact (min_le_right _ _).trans
        ((min_le_right _ _).trans
          ((min_le_right _ _).trans
            ((min_le_right _ _).trans (min_le_right _ _)))))
  exact ⟨eval_eq_zero_or_mul_pos_of_endpointStabilityWidth A root
      hxLower hxUpper hyLower hyUpper hA,
    eval_eq_zero_or_mul_pos_of_endpointStabilityWidth B root
      hxLower hxUpper hyLower hyUpper hB,
    eval_eq_zero_or_mul_pos_of_endpointStabilityWidth C root
      hxLower hxUpper hyLower hyUpper hC,
    eval_eq_zero_or_mul_pos_of_endpointStabilityWidth D root
      hxLower hxUpper hyLower hyUpper hD,
    eval_eq_zero_or_mul_pos_of_endpointStabilityWidth
      (productNumerator A B C D) root
      hxLower hxUpper hyLower hyUpper hE,
    eval_eq_zero_or_mul_pos_of_endpointStabilityWidth
      (productDenominator A B C D) root
      hxLower hxUpper hyLower hyUpper hH⟩

/-- Quantitative statement that two nonzero complex endpoint vectors turn by
less than the rational cone with slope `1/3`.  The dot/cross formulation
avoids angles, trigonometric functions, and square roots. -/
def NarrowComplexTurn
    (Aₗ Bₗ Aᵣ Bᵣ : ℚ) : Prop :=
  3 * |Aₗ * Bᵣ - Bₗ * Aᵣ| < Aₗ * Aᵣ + Bₗ * Bᵣ

theorem complexDot_pos_of_narrowComplexTurn
    {Aₗ Bₗ Aᵣ Bᵣ : ℚ}
    (hnarrow : NarrowComplexTurn Aₗ Bₗ Aᵣ Bᵣ) :
    0 < Aₗ * Aᵣ + Bₗ * Bᵣ := by
  unfold NarrowComplexTurn at hnarrow
  exact (mul_nonneg (by norm_num) (abs_nonneg _)).trans_lt hnarrow

/-- Two slope-`1/3` factor turns make the endpoint product vectors have
positive dot product.  This is the square-root-free form of saying that the
sum of their two small angular turns is still below a quarter turn. -/
theorem productComplexDot_pos_of_narrowTurns
    {Aₗ Bₗ Cₗ Dₗ Aᵣ Bᵣ Cᵣ Dᵣ : ℚ}
    (hleft : NarrowComplexTurn Aₗ Bₗ Aᵣ Bᵣ)
    (hright : NarrowComplexTurn Cₗ Dₗ Cᵣ Dᵣ) :
    0 <
      (Aₗ * Cₗ - Bₗ * Dₗ) * (Aᵣ * Cᵣ - Bᵣ * Dᵣ) +
      (Aₗ * Dₗ + Bₗ * Cₗ) * (Aᵣ * Dᵣ + Bᵣ * Cᵣ) := by
  let leftDot := Aₗ * Aᵣ + Bₗ * Bᵣ
  let leftCross := Aₗ * Bᵣ - Bₗ * Aᵣ
  let rightDot := Cₗ * Cᵣ + Dₗ * Dᵣ
  let rightCross := Cₗ * Dᵣ - Dₗ * Cᵣ
  have hleftDot : 0 < leftDot :=
    complexDot_pos_of_narrowComplexTurn hleft
  have hrightDot : 0 < rightDot :=
    complexDot_pos_of_narrowComplexTurn hright
  have hleftCross : |leftCross| < leftDot / 3 := by
    unfold NarrowComplexTurn at hleft
    dsimp only [leftDot, leftCross]
    linarith
  have hrightCross : |rightCross| < rightDot / 3 := by
    unfold NarrowComplexTurn at hright
    dsimp only [rightDot, rightCross]
    linarith
  have habsCrossProduct : |leftCross * rightCross| <
      (leftDot / 3) * (rightDot / 3) := by
    rw [abs_mul]
    calc
      |leftCross| * |rightCross| ≤
          (leftDot / 3) * |rightCross| :=
        mul_le_mul_of_nonneg_right hleftCross.le (abs_nonneg _)
      _ < (leftDot / 3) * (rightDot / 3) :=
        mul_lt_mul_of_pos_left hrightCross (by linarith [hleftDot])
  have hcrossProduct : leftCross * rightCross < leftDot * rightDot := by
    calc
      leftCross * rightCross ≤ |leftCross * rightCross| := le_abs_self _
      _ < (leftDot / 3) * (rightDot / 3) := habsCrossProduct
      _ < leftDot * rightDot := by
        nlinarith [mul_pos hleftDot hrightDot]
  have hidentity :
      (Aₗ * Cₗ - Bₗ * Dₗ) * (Aᵣ * Cᵣ - Bᵣ * Dᵣ) +
          (Aₗ * Dₗ + Bₗ * Cₗ) * (Aᵣ * Dᵣ + Bᵣ * Cᵣ) =
        leftDot * rightDot - leftCross * rightCross := by
    dsimp only [leftDot, leftCross, rightDot, rightCross]
    ring
  rw [hidentity]
  linarith

/-- The oriented turn of a complex product is the sign-compatible sum of
the two factor turns; positive endpoint dots are harmless positive scales. -/
theorem productTurn_sumCompatible_of_narrowTurns
    {Aₗ Bₗ Cₗ Dₗ Aᵣ Bᵣ Cᵣ Dᵣ : ℚ}
    (hleft : NarrowComplexTurn Aₗ Bₗ Aᵣ Bᵣ)
    (hright : NarrowComplexTurn Cₗ Dₗ Cᵣ Dᵣ) :
    FiniteSign.SumCompatible
      (FiniteSign.ofRat (Aₗ * Bᵣ - Bₗ * Aᵣ))
      (FiniteSign.ofRat (Cₗ * Dᵣ - Dₗ * Cᵣ))
      (FiniteSign.ofRat
        ((Aₗ * Cₗ - Bₗ * Dₗ) * (Aᵣ * Dᵣ + Bᵣ * Cᵣ) -
          (Aₗ * Dₗ + Bₗ * Cₗ) * (Aᵣ * Cᵣ - Bᵣ * Dᵣ))) := by
  let leftDot := Aₗ * Aᵣ + Bₗ * Bᵣ
  let leftCross := Aₗ * Bᵣ - Bₗ * Aᵣ
  let rightDot := Cₗ * Cᵣ + Dₗ * Dᵣ
  let rightCross := Cₗ * Dᵣ - Dₗ * Cᵣ
  have hleftDot : 0 < leftDot :=
    complexDot_pos_of_narrowComplexTurn hleft
  have hrightDot : 0 < rightDot :=
    complexDot_pos_of_narrowComplexTurn hright
  have hsum := FiniteSign.sumCompatible_ofRat
    (leftCross * rightDot) (leftDot * rightCross)
  have hleftScale : FiniteSign.ofRat (leftCross * rightDot) =
      FiniteSign.ofRat leftCross := by
    rw [FiniteSign.ofRat_mul, FiniteSign.ofRat_of_pos hrightDot]
    cases FiniteSign.ofRat leftCross <;> rfl
  have hrightScale : FiniteSign.ofRat (leftDot * rightCross) =
      FiniteSign.ofRat rightCross := by
    rw [FiniteSign.ofRat_mul, FiniteSign.ofRat_of_pos hleftDot]
    cases FiniteSign.ofRat rightCross <;> rfl
  have hcrossIdentity :
      leftCross * rightDot + leftDot * rightCross =
        (Aₗ * Cₗ - Bₗ * Dₗ) * (Aᵣ * Dᵣ + Bᵣ * Cᵣ) -
          (Aₗ * Dₗ + Bₗ * Cₗ) * (Aᵣ * Cᵣ - Bᵣ * Dᵣ) := by
    dsimp only [leftDot, leftCross, rightDot, rightCross]
    ring
  rw [hleftScale, hrightScale, hcrossIdentity] at hsum
  exact hsum

/-- A positive coefficient-only width forcing a displayed coprime complex
polynomial pair to make a narrow turn on every nested rational cell. -/
def coprimeNarrowTurnWidthResolution
    {A B : RatPolynomial}
    (coprime : FTA.DenseSquarefree.CoprimeCertificate A B)
    (root : FTA.SturmTransducer.RationalInterval) : ℚ :=
  let bound := intervalMagnitude root.lower root.upper
  let margin := coprimeExclusionMargin coprime bound
  let valueMajorant := max 1
    (denseEvalAbsBound A bound + denseEvalAbsBound B bound)
  let slopeMajorant := max 1
    (denseEvalLipschitzBound A bound +
      denseEvalLipschitzBound B bound)
  margin ^ 2 / (4 * valueMajorant * slopeMajorant)

theorem coprimeNarrowTurnWidthResolution_pos
    {A B : RatPolynomial}
    (coprime : FTA.DenseSquarefree.CoprimeCertificate A B)
    (root : FTA.SturmTransducer.RationalInterval) :
    0 < coprimeNarrowTurnWidthResolution coprime root := by
  let bound := intervalMagnitude root.lower root.upper
  let margin := coprimeExclusionMargin coprime bound
  let valueMajorant := max 1
    (denseEvalAbsBound A bound + denseEvalAbsBound B bound)
  let slopeMajorant := max 1
    (denseEvalLipschitzBound A bound +
      denseEvalLipschitzBound B bound)
  have hbound : 0 ≤ bound :=
    (intervalMagnitude_pos root.lower root.upper).le
  have hmargin : 0 < margin := coprimeExclusionMargin_pos coprime hbound
  have hvalue : 0 < valueMajorant :=
    zero_lt_one.trans_le (le_max_left _ _)
  have hslope : 0 < slopeMajorant :=
    zero_lt_one.trans_le (le_max_left _ _)
  dsimp only [coprimeNarrowTurnWidthResolution]
  exact div_pos (sq_pos_of_pos hmargin)
    (mul_pos (mul_pos (by norm_num) hvalue) hslope)

/-- Below the displayed coefficient width, the exact rational endpoint
vectors of a coprime pair satisfy `NarrowComplexTurn`.  The proof uses only
the dense Lipschitz bounds and the rational Bezout exclusion margin. -/
theorem narrowComplexTurn_of_coprime_refined_width
    {A B : RatPolynomial}
    (coprime : FTA.DenseSquarefree.CoprimeCertificate A B)
    (root interval : FTA.SturmTransducer.RationalInterval)
    (hrefines : interval.Refines root) (proper : interval.Proper)
    (hwidth : interval.width <
      coprimeNarrowTurnWidthResolution coprime root) :
    NarrowComplexTurn
      (A.eval interval.lower) (B.eval interval.lower)
      (A.eval interval.upper) (B.eval interval.upper) := by
  let bound := intervalMagnitude root.lower root.upper
  let margin := coprimeExclusionMargin coprime bound
  let valueMajorant := max 1
    (denseEvalAbsBound A bound + denseEvalAbsBound B bound)
  let slopeMajorant := max 1
    (denseEvalLipschitzBound A bound +
      denseEvalLipschitzBound B bound)
  let width := interval.width
  let Aₗ := A.eval interval.lower
  let Bₗ := B.eval interval.lower
  let Aᵣ := A.eval interval.upper
  let Bᵣ := B.eval interval.upper
  let deltaA := Aᵣ - Aₗ
  let deltaB := Bᵣ - Bₗ
  let errorBound := valueMajorant * (slopeMajorant * width)
  have hbound : 0 ≤ bound :=
    (intervalMagnitude_pos root.lower root.upper).le
  have hwidthNonneg : 0 ≤ width := interval.width_pos proper |>.le
  have hlowerBound : |interval.lower| ≤ bound := by
    apply abs_le_intervalMagnitude
    · exact hrefines.1
    · exact proper.le.trans hrefines.2
  have hupperBound : |interval.upper| ≤ bound := by
    apply abs_le_intervalMagnitude
    · exact hrefines.1.trans proper.le
    · exact hrefines.2
  have hmarginPos : 0 < margin :=
    coprimeExclusionMargin_pos coprime hbound
  have hvaluePos : 0 < valueMajorant :=
    zero_lt_one.trans_le (le_max_left _ _)
  have hslopePos : 0 < slopeMajorant :=
    zero_lt_one.trans_le (le_max_left _ _)
  have hALower : |Aₗ| ≤ denseEvalAbsBound A bound := by
    exact abs_dense_eval_le_denseEvalAbsBound A hbound hlowerBound
  have hBLower : |Bₗ| ≤ denseEvalAbsBound B bound := by
    exact abs_dense_eval_le_denseEvalAbsBound B hbound hlowerBound
  have hvalue : |Aₗ| + |Bₗ| ≤ valueMajorant := by
    exact (add_le_add hALower hBLower).trans (le_max_right _ _)
  have hdeltaA : |deltaA| ≤
      denseEvalLipschitzBound A bound * width := by
    change |A.eval interval.upper - A.eval interval.lower| ≤
      denseEvalLipschitzBound A bound *
        (interval.upper - interval.lower)
    simpa only [abs_of_nonneg (sub_nonneg.mpr proper.le)] using
      abs_dense_eval_sub_eval_le_dense A hbound hupperBound hlowerBound
  have hdeltaB : |deltaB| ≤
      denseEvalLipschitzBound B bound * width := by
    change |B.eval interval.upper - B.eval interval.lower| ≤
      denseEvalLipschitzBound B bound *
        (interval.upper - interval.lower)
    simpa only [abs_of_nonneg (sub_nonneg.mpr proper.le)] using
      abs_dense_eval_sub_eval_le_dense B hbound hupperBound hlowerBound
  have hslopeSumNonneg : 0 ≤
      denseEvalLipschitzBound A bound +
        denseEvalLipschitzBound B bound := by
    exact add_nonneg (denseHornerBounds_nonneg A hbound).2
      (denseHornerBounds_nonneg B hbound).2
  have hdelta : |deltaA| + |deltaB| ≤ slopeMajorant * width := by
    calc
      |deltaA| + |deltaB| ≤
          denseEvalLipschitzBound A bound * width +
            denseEvalLipschitzBound B bound * width :=
        add_le_add hdeltaA hdeltaB
      _ = (denseEvalLipschitzBound A bound +
            denseEvalLipschitzBound B bound) * width := by ring
      _ ≤ slopeMajorant * width := by
        gcongr
        exact le_max_right _ _
  have hmarginMax : margin ≤ max |Aₗ| |Bₗ| :=
    coprimeExclusionMargin_le_max_abs_eval coprime hbound hlowerBound
  have hnormLower : margin ^ 2 ≤ Aₗ ^ 2 + Bₗ ^ 2 := by
    rcases le_max_iff.mp hmarginMax with hA | hB
    · have hA2 := pow_le_pow_left₀ hmarginPos.le hA 2
      rw [sq_abs] at hA2
      exact hA2.trans (le_add_of_nonneg_right (sq_nonneg _))
    · have hB2 := pow_le_pow_left₀ hmarginPos.le hB 2
      rw [sq_abs] at hB2
      exact hB2.trans (le_add_of_nonneg_left (sq_nonneg _))
  have hcrossIdentity :
      Aₗ * Bᵣ - Bₗ * Aᵣ = Aₗ * deltaB - Bₗ * deltaA := by
    dsimp only [deltaA, deltaB]
    ring
  have hcross : |Aₗ * Bᵣ - Bₗ * Aᵣ| ≤ errorBound := by
    rw [hcrossIdentity]
    calc
      |Aₗ * deltaB - Bₗ * deltaA| ≤
          |Aₗ * deltaB| + |Bₗ * deltaA| := by
        simpa only [sub_eq_add_neg, abs_neg] using
          abs_add_le (Aₗ * deltaB) (-(Bₗ * deltaA))
      _ = |Aₗ| * |deltaB| + |Bₗ| * |deltaA| := by
        rw [abs_mul, abs_mul]
      _ ≤ (|Aₗ| + |Bₗ|) * (|deltaA| + |deltaB|) := by
        nlinarith [mul_nonneg (abs_nonneg Aₗ) (abs_nonneg deltaA),
          mul_nonneg (abs_nonneg Bₗ) (abs_nonneg deltaB)]
      _ ≤ valueMajorant * (slopeMajorant * width) := by
        exact mul_le_mul hvalue hdelta
          (add_nonneg (abs_nonneg _) (abs_nonneg _)) hvaluePos.le
      _ = errorBound := rfl
  have hdotIdentity :
      Aₗ * Aᵣ + Bₗ * Bᵣ =
        Aₗ ^ 2 + Bₗ ^ 2 + (Aₗ * deltaA + Bₗ * deltaB) := by
    dsimp only [deltaA, deltaB]
    ring
  have hdotError : |Aₗ * deltaA + Bₗ * deltaB| ≤ errorBound := by
    calc
      |Aₗ * deltaA + Bₗ * deltaB| ≤
          |Aₗ * deltaA| + |Bₗ * deltaB| := abs_add_le _ _
      _ = |Aₗ| * |deltaA| + |Bₗ| * |deltaB| := by
        rw [abs_mul, abs_mul]
      _ ≤ (|Aₗ| + |Bₗ|) * (|deltaA| + |deltaB|) := by
        nlinarith [mul_nonneg (abs_nonneg Aₗ) (abs_nonneg deltaB),
          mul_nonneg (abs_nonneg Bₗ) (abs_nonneg deltaA)]
      _ ≤ valueMajorant * (slopeMajorant * width) := by
        exact mul_le_mul hvalue hdelta
          (add_nonneg (abs_nonneg _) (abs_nonneg _)) hvaluePos.le
      _ = errorBound := rfl
  have hdot : margin ^ 2 - errorBound ≤
      Aₗ * Aᵣ + Bₗ * Bᵣ := by
    rw [hdotIdentity]
    have hlowerError : -errorBound ≤ Aₗ * deltaA + Bₗ * deltaB :=
      neg_le_of_abs_le hdotError
    linarith
  have hdenominator : 0 < 4 * valueMajorant * slopeMajorant :=
    mul_pos (mul_pos (by norm_num) hvaluePos) hslopePos
  have hscaled : 4 * errorBound < margin ^ 2 := by
    have hraw := (lt_div_iff₀ hdenominator).mp (by
      simpa only [coprimeNarrowTurnWidthResolution, bound, margin,
        valueMajorant, slopeMajorant, width] using hwidth)
    dsimp only [errorBound]
    nlinarith
  unfold NarrowComplexTurn
  nlinarith


end FTA.CauchyProduct
