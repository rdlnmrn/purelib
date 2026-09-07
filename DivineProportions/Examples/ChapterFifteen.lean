import DivineProportions.Algebra.FieldEleven
import DivineProportions.Conics.Quadrola
import DivineProportions.Conics.Grammola
import mathlib.RFAP.ConstructiveFraction

/-!
# Divine Proportions, Chapter 15 worked examples

This module records the book's concrete finite-field conics separately from
the generic constructive proofs.  In particular, Example 15.6 is checked in
the executable eleven-element field without enumerating that field globally.
-/

namespace DivineProportions

namespace ChapterFifteenExamples

variable {K : Type*} [RFAP.ExplicitField K]

/-- Two conic representatives whose six coefficients differ by one nonzero
scale have exactly the same locus.  This is the quotient-free finite meaning
of equality of the book's conic proportions. -/
private theorem conic_contains_iff_of_coefficient_scale
    (source target : Conic K) (scale : K) (scaleNonzero : scale ≠ 0)
    (dScale : source.d = scale * target.d)
    (eScale : source.e = scale * target.e)
    (fScale : source.f = scale * target.f)
    (aScale : source.a = scale * target.a)
    (bScale : source.b = scale * target.b)
    (cScale : source.c = scale * target.c)
    (point : Point K) :
    source.Contains point ↔ target.Contains point := by
  have evaluationScale :
      source.evaluate point = scale * target.evaluate point := by
    unfold Conic.evaluate
    rw [dScale, eScale, fScale, aScale, bScale, cScale]
    ring1
  have scaleCancel : scale⁻¹ * scale = (1 : K) := by
    calc
      scale⁻¹ * scale = scale * scale⁻¹ := by ring1
      _ = 1 := RFAP.ExplicitField.mul_inv_cancel scale scaleNonzero
  constructor
  · intro sourceContains
    unfold Conic.Contains at sourceContains ⊢
    have productZero : scale * target.evaluate point = 0 := by
      rw [← evaluationScale]
      exact sourceContains
    calc
      target.evaluate point = 1 * target.evaluate point := by ring1
      _ = (scale⁻¹ * scale) * target.evaluate point := by rw [scaleCancel]
      _ = scale⁻¹ * (scale * target.evaluate point) := by ring1
      _ = 0 := by rw [productZero]; ring1
  · intro targetContains
    unfold Conic.Contains at targetContains ⊢
    rw [evaluationScale, targetContains]
    ring1

namespace ExampleFifteenSix

open FieldEleven

abbrev F₁₁ := FieldEleven.Element

/-- The two displayed foci `[1,0]` and `[-1,0]`. -/
def firstFocus : Point F₁₁ := ⟨1, 0⟩

def secondFocus : Point F₁₁ := ⟨-1, 0⟩

theorem associated_nonzero : (1 : F₁₁) ≠ 0 := by decide

theorem eight_nonzero : (8 : F₁₁) ≠ 0 := by decide

/-- The displayed data satisfy all four clauses in the definition of a
quadrola. -/
theorem presentation : Quadrola.Presentation firstFocus secondFocus 1 := by
  constructor
  · intro equal
    have xEqual := congrArg Point.x equal
    change (1 : F₁₁) = -1 at xEqual
    exact (by decide : (1 : F₁₁) ≠ -1) xEqual
  · exact associated_nonzero
  · unfold quadrance firstFocus secondFocus
    decide
  · unfold quadrance firstFocus secondFocus
    decide

/-- The executable conic obtained directly from the Archimedes equation. -/
def quadrolaConic : Conic F₁₁ :=
  Quadrola.conic firstFocus secondFocus 1 associated_nonzero eight_nonzero

/-- The representative `⟨7:0:5:0:0:1⟩` printed in Example 15.6. -/
def printedConic : Conic F₁₁ where
  d := 7
  e := 0
  f := 5
  a := 0
  b := 0
  c := 1
  quadratic_nonzero := Or.inl (by decide)

/-- The constructed coefficients are three times the printed representative.
This is the exact finite meaning of equality of the two conic proportions. -/
theorem coefficient_scale :
    quadrolaConic.d = 3 * printedConic.d ∧
      quadrolaConic.e = 3 * printedConic.e ∧
      quadrolaConic.f = 3 * printedConic.f ∧
      quadrolaConic.a = 3 * printedConic.a ∧
      quadrolaConic.b = 3 * printedConic.b ∧
      quadrolaConic.c = 3 * printedConic.c := by
  unfold quadrolaConic printedConic Quadrola.conic Quadrola.conicD
    Quadrola.conicE Quadrola.conicF Quadrola.conicA Quadrola.conicB
    Quadrola.conicC firstFocus secondFocus
  decide

/-- Example 15.6: the quadrola locus is exactly the printed conic
`7x²+5y²+1=0` in `F₁₁`. -/
theorem example_15_6 (point : Point F₁₁) :
    Quadrola.Contains firstFocus secondFocus 1 point ↔
      printedConic.Contains point := by
  have definingEquation :
      Quadrola.Contains firstFocus secondFocus 1 point ↔
        quadrolaConic.Contains point := by
    unfold Quadrola.Contains Conic.Contains quadrolaConic
    rw [Quadrola.conic_evaluate]
  rcases coefficient_scale with ⟨dScale, eScale, fScale, aScale, bScale,
    cScale⟩
  have sameLocus := conic_contains_iff_of_coefficient_scale
    quadrolaConic printedConic 3 (by decide) dScale eScale fScale aScale
      bScale cScale point
  exact definingEquation.trans sameLocus

end ExampleFifteenSix

private theorem one_nonzero_of_two_nonzero
    (twoNonzero : (2 : K) ≠ 0) : (1 : K) ≠ 0 := by
  intro oneZero
  apply twoNonzero
  calc
    (2 : K) = 2 * 1 := by ring1
    _ = 0 := by rw [oneZero]; ring1

private def halfFirstDiagonal (twoNonzero : (2 : K) ≠ 0) : Line K where
  a := 1 / 2
  b := -1
  c := 0
  direction_nonzero := Or.inr (by
    intro negativeOneZero
    apply one_nonzero_of_two_nonzero twoNonzero
    calc
      (1 : K) = -(-1) := by ring1
      _ = 0 := by rw [negativeOneZero]; ring1)

private def halfSecondDiagonal (twoNonzero : (2 : K) ≠ 0) : Line K where
  a := 1 / 2
  b := 1
  c := 0
  direction_nonzero := Or.inr (one_nonzero_of_two_nonzero twoNonzero)

private def integerFirstDiagonal (twoNonzero : (2 : K) ≠ 0) : Line K where
  a := 1
  b := -2
  c := 0
  direction_nonzero := Or.inl (one_nonzero_of_two_nonzero twoNonzero)

private def integerSecondDiagonal (twoNonzero : (2 : K) ≠ 0) : Line K where
  a := 1
  b := 2
  c := 0
  direction_nonzero := Or.inl (one_nonzero_of_two_nonzero twoNonzero)

private theorem half_diagonals_equivalent
    (twoNonzero : (2 : K) ≠ 0) :
    (halfFirstDiagonal twoNonzero).Equivalent
        (integerFirstDiagonal twoNonzero) ∧
      (halfSecondDiagonal twoNonzero).Equivalent
        (integerSecondDiagonal twoNonzero) := by
  have twoCancel : (2 : K) * (2 : K)⁻¹ = 1 :=
    RFAP.ExplicitField.mul_inv_cancel 2 twoNonzero
  unfold halfFirstDiagonal halfSecondDiagonal integerFirstDiagonal
    integerSecondDiagonal Line.Equivalent
  simp only [RFAP.ExplicitField.div_eq_mul_inv]
  refine ⟨⟨?_, by ring1, by ring1⟩, ⟨?_, by ring1, by ring1⟩⟩
  · calc
      ((1 : K) * (2 : K)⁻¹) * -2 =
          -(2 * (2 : K)⁻¹) := by ring1
      _ = -1 := by rw [twoCancel]
      _ = 1 * -1 := by ring1
  · calc
      ((1 : K) * (2 : K)⁻¹) * 2 =
          2 * (2 : K)⁻¹ := by ring1
      _ = 1 := twoCancel
      _ = 1 * 1 := by ring1

namespace ExampleFifteenEight

abbrev Rational := RFAP.ConstructiveFraction.Rational

/-- The printed diagonal `x-2y=0`. -/
def firstDiagonal : Line Rational where
  a := 1
  b := -2
  c := 0
  direction_nonzero := Or.inl (by decide)

/-- The printed diagonal `x+2y=0`. -/
def secondDiagonal : Line Rational where
  a := 1
  b := 2
  c := 0
  direction_nonzero := Or.inl (by decide)

theorem first_nonNull : ¬ firstDiagonal.IsNull := by
  unfold Line.IsNull firstDiagonal
  decide

theorem second_nonNull : ¬ secondDiagonal.IsNull := by
  unfold Line.IsNull secondDiagonal
  decide

theorem two_nonzero : (2 : Rational) ≠ 0 := by decide

/-- The exact `a=1/2` normalization of the first Example 15.7 diagonal. -/
def normalizedFirstDiagonal : Line Rational where
  a := (halfFirstDiagonal two_nonzero).a
  b := (halfFirstDiagonal two_nonzero).b
  c := (halfFirstDiagonal two_nonzero).c
  direction_nonzero := (halfFirstDiagonal two_nonzero).direction_nonzero

/-- The exact `a=1/2` normalization of the second Example 15.7 diagonal. -/
def normalizedSecondDiagonal : Line Rational where
  a := (halfSecondDiagonal two_nonzero).a
  b := (halfSecondDiagonal two_nonzero).b
  c := (halfSecondDiagonal two_nonzero).c
  direction_nonzero := (halfSecondDiagonal two_nonzero).direction_nonzero

/-- The exact rational data satisfy the grammola definition. -/
theorem presentation : Grammola.Presentation firstDiagonal secondDiagonal 1 := by
  refine ⟨first_nonNull, second_nonNull, ?_, ?_, by decide⟩
  · unfold Line.Parallel firstDiagonal secondDiagonal
    decide
  · unfold Line.Perpendicular firstDiagonal secondDiagonal
    decide

/-- The cleared metric construction before rescaling its six coefficients. -/
def constructedConic : Conic Rational :=
  Grammola.conic firstDiagonal secondDiagonal first_nonNull second_nonNull 1
    two_nonzero

/-- Example 15.8's conic `2x²+8y²=5`. -/
def printedConic : Conic Rational where
  d := 2
  e := 0
  f := 8
  a := 0
  b := 0
  c := -5
  quadratic_nonzero := Or.inl (by decide)

/-- Clearing the two line norms produces five times the printed conic. -/
theorem coefficient_scale :
    constructedConic.d = 5 * printedConic.d ∧
      constructedConic.e = 5 * printedConic.e ∧
      constructedConic.f = 5 * printedConic.f ∧
      constructedConic.a = 5 * printedConic.a ∧
      constructedConic.b = 5 * printedConic.b ∧
      constructedConic.c = 5 * printedConic.c := by
  unfold constructedConic printedConic Grammola.conic Grammola.conicD
    Grammola.conicE Grammola.conicF Grammola.conicA Grammola.conicB
    Grammola.conicC lineNorm firstDiagonal secondDiagonal
  decide

/-- The `a=1/2` representatives in Example 15.7 are the same two lines as
the integer representatives printed in Example 15.8. -/
theorem normalized_diagonals :
    normalizedFirstDiagonal.Equivalent firstDiagonal ∧
      normalizedSecondDiagonal.Equivalent secondDiagonal := by
  simpa only [normalizedFirstDiagonal, normalizedSecondDiagonal, firstDiagonal,
    secondDiagonal, integerFirstDiagonal, integerSecondDiagonal] using
      (half_diagonals_equivalent (K := Rational) two_nonzero)

theorem printed_equation (point : Point Rational) :
    printedConic.Contains point ↔
      2 * point.x ^ 2 + 8 * point.y ^ 2 = 5 := by
  unfold Conic.Contains
  constructor
  · intro polynomialZero
    change
      2 * point.x ^ 2 + 0 * point.x * point.y + 8 * point.y ^ 2 +
        0 * point.x + 0 * point.y + (-5) = 0 at polynomialZero
    calc
      2 * point.x ^ 2 + 8 * point.y ^ 2 =
          (2 * point.x ^ 2 + 0 * point.x * point.y +
            8 * point.y ^ 2 + 0 * point.x + 0 * point.y + (-5)) + 5 := by
        ring1
      _ = 5 := by rw [polynomialZero]; ring1
  · intro equation
    change
      2 * point.x ^ 2 + 0 * point.x * point.y + 8 * point.y ^ 2 +
        0 * point.x + 0 * point.y + (-5) = 0
    calc
      2 * point.x ^ 2 + 0 * point.x * point.y +
          8 * point.y ^ 2 + 0 * point.x + 0 * point.y + (-5) =
        (2 * point.x ^ 2 + 8 * point.y ^ 2) - 5 := by ring1
      _ = 0 := by rw [equation]; ring1

/-- Example 15.8: the exact rational grammola equation is the displayed
conic `2x²+8y²=5`. -/
theorem example_15_8 (point : Point Rational) :
    Grammola.Contains firstDiagonal secondDiagonal first_nonNull second_nonNull
        1 point ↔
      2 * point.x ^ 2 + 8 * point.y ^ 2 = 5 := by
  have metricToConstructed :=
    (Grammola.conic_contains_iff firstDiagonal secondDiagonal first_nonNull
      second_nonNull 1 two_nonzero point).symm
  rcases coefficient_scale with ⟨dScale, eScale, fScale, aScale, bScale,
    cScale⟩
  have constructedToPrinted := conic_contains_iff_of_coefficient_scale
    constructedConic printedConic 5 (by decide) dScale eScale fScale aScale
      bScale cScale point
  exact metricToConstructed.trans (constructedToPrinted.trans (printed_equation point))

end ExampleFifteenEight

/-- Example 15.8's four distinguished points, stated over any constructive
field in which a displayed square root of five is supplied. -/
theorem example_15_8_distinguished_points
    (root : K) (rootSquare : root ^ 2 = 5)
    (twoNonzero : (2 : K) ≠ 0) (fourNonzero : (4 : K) ≠ 0) :
    let x := root / 2
    let y := root / 4
    2 * x ^ 2 + 8 * y ^ 2 = 5 ∧
      2 * x ^ 2 + 8 * (-y) ^ 2 = 5 ∧
      2 * (-x) ^ 2 + 8 * y ^ 2 = 5 ∧
      2 * (-x) ^ 2 + 8 * (-y) ^ 2 = 5 := by
  dsimp only
  have twoCancel : (2 : K) * (2 : K)⁻¹ = 1 :=
    RFAP.ExplicitField.mul_inv_cancel 2 twoNonzero
  have fourCancel : (4 : K) * (4 : K)⁻¹ = 1 :=
    RFAP.ExplicitField.mul_inv_cancel 4 fourNonzero
  have candidateFourCancel :
      (4 : K) * ((2 : K)⁻¹ * (2 : K)⁻¹) = 1 := by
    calc
      (4 : K) * ((2 : K)⁻¹ * (2 : K)⁻¹) =
          (2 * (2 : K)⁻¹) ^ 2 := by ring1
      _ = 1 := by rw [twoCancel]; ring1
  have inverseFour : (4 : K)⁻¹ = (2 : K)⁻¹ * (2 : K)⁻¹ := by
    calc
      (4 : K)⁻¹ = 1 * (4 : K)⁻¹ := by ring1
      _ = (4 * ((2 : K)⁻¹ * (2 : K)⁻¹)) * (4 : K)⁻¹ := by
        rw [candidateFourCancel]
      _ = ((2 : K)⁻¹ * (2 : K)⁻¹) * (4 * (4 : K)⁻¹) := by
        ring1
      _ = (2 : K)⁻¹ * (2 : K)⁻¹ := by rw [fourCancel]; ring1
  have positive :
      2 * (root / 2) ^ 2 + 8 * (root / 4) ^ 2 = 5 := by
    simp only [RFAP.ExplicitField.div_eq_mul_inv, inverseFour]
    calc
      2 * (root * (2 : K)⁻¹) ^ 2 +
          8 * (root * ((2 : K)⁻¹ * (2 : K)⁻¹)) ^ 2 =
        root ^ 2 + root ^ 2 * (2 * (2 : K)⁻¹ - 1) *
          (4 * (2 : K)⁻¹ ^ 3 + 2 * (2 : K)⁻¹ ^ 2 +
            2 * (2 : K)⁻¹ + 1) := by ring1
      _ = root ^ 2 := by rw [twoCancel]; ring1
      _ = 5 := rootSquare
  exact ⟨positive, by simpa only [neg_sq] using positive,
    by simpa only [neg_sq] using positive,
    by simpa only [neg_sq] using positive⟩

namespace ExampleFifteenNine

open FieldEleven

abbrev F₁₁ := FieldEleven.Element

def firstDiagonal : Line F₁₁ where
  a := 1
  b := -2
  c := 0
  direction_nonzero := Or.inl (by decide)

def secondDiagonal : Line F₁₁ where
  a := 1
  b := 2
  c := 0
  direction_nonzero := Or.inl (by decide)

theorem first_nonNull : ¬ firstDiagonal.IsNull := by
  unfold Line.IsNull firstDiagonal
  decide

theorem second_nonNull : ¬ secondDiagonal.IsNull := by
  unfold Line.IsNull secondDiagonal
  decide

theorem two_nonzero : (2 : F₁₁) ≠ 0 := by decide

theorem presentation : Grammola.Presentation firstDiagonal secondDiagonal 1 := by
  refine ⟨first_nonNull, second_nonNull, ?_, ?_, by decide⟩
  · unfold Line.Parallel firstDiagonal secondDiagonal
    decide
  · unfold Line.Perpendicular firstDiagonal secondDiagonal
    decide

def constructedConic : Conic F₁₁ :=
  Grammola.conic firstDiagonal secondDiagonal first_nonNull second_nonNull 1
    two_nonzero

/-- The `F₁₁` representative `2x²+8y²-5=0`. -/
def printedConic : Conic F₁₁ where
  d := 2
  e := 0
  f := 8
  a := 0
  b := 0
  c := -5
  quadratic_nonzero := Or.inl (by decide)

theorem coefficient_scale :
    constructedConic.d = 5 * printedConic.d ∧
      constructedConic.e = 5 * printedConic.e ∧
      constructedConic.f = 5 * printedConic.f ∧
      constructedConic.a = 5 * printedConic.a ∧
      constructedConic.b = 5 * printedConic.b ∧
      constructedConic.c = 5 * printedConic.c := by
  unfold constructedConic printedConic Grammola.conic Grammola.conicD
    Grammola.conicE Grammola.conicF Grammola.conicA Grammola.conicB
    Grammola.conicC lineNorm firstDiagonal secondDiagonal
  decide

def point21 : Point F₁₁ := ⟨2, 1⟩
def point2Neg1 : Point F₁₁ := ⟨2, -1⟩
def pointNeg21 : Point F₁₁ := ⟨-2, 1⟩
def pointNeg2Neg1 : Point F₁₁ := ⟨-2, -1⟩

/-- Example 15.9: the four displayed points lie on the grammola and split
between its two displayed diagonal lines exactly as in the figure. -/
theorem example_15_9 :
    printedConic.Contains point21 ∧ printedConic.Contains point2Neg1 ∧
      printedConic.Contains pointNeg21 ∧
      printedConic.Contains pointNeg2Neg1 ∧
      firstDiagonal.Contains point21 ∧
      firstDiagonal.Contains pointNeg2Neg1 ∧
      secondDiagonal.Contains point2Neg1 ∧
      secondDiagonal.Contains pointNeg21 := by
  unfold Conic.Contains Conic.evaluate Line.Contains printedConic firstDiagonal
    secondDiagonal point21 point2Neg1 pointNeg21 pointNeg2Neg1
  decide

/-- The metrical `F₁₁` grammola and the printed conic have the same
locus. -/
theorem metric_locus (point : Point F₁₁) :
    Grammola.Contains firstDiagonal secondDiagonal first_nonNull second_nonNull
        1 point ↔
      printedConic.Contains point := by
  have metricToConstructed :=
    (Grammola.conic_contains_iff firstDiagonal secondDiagonal first_nonNull
      second_nonNull 1 two_nonzero point).symm
  rcases coefficient_scale with ⟨dScale, eScale, fScale, aScale, bScale,
    cScale⟩
  have constructedToPrinted := conic_contains_iff_of_coefficient_scale
    constructedConic printedConic 5 (by decide) dScale eScale fScale aScale
      bScale cScale point
  exact metricToConstructed.trans constructedToPrinted

end ExampleFifteenNine

namespace ExerciseFifteenSixteen

open FieldEleven

abbrev F₁₁ := FieldEleven.Element

/-- A focal pair for the printed grammola: its vertical separation has
quadrance nine. -/
def firstFocus : Point F₁₁ := ⟨0, 4⟩

def secondFocus : Point F₁₁ := ⟨0, 7⟩

theorem associated_nonzero : (8 : F₁₁) ≠ 0 := by decide

theorem eight_nonzero : (8 : F₁₁) ≠ 0 := by decide

/-- The counterexample's focal data satisfy every quadrola nondegeneracy
clause. -/
theorem presentation : Quadrola.Presentation firstFocus secondFocus 8 := by
  constructor
  · intro equal
    have yEqual := congrArg Point.y equal
    change (4 : F₁₁) = 7 at yEqual
    exact (by decide : (4 : F₁₁) ≠ 7) yEqual
  · exact associated_nonzero
  · unfold quadrance firstFocus secondFocus
    decide
  · unfold quadrance firstFocus secondFocus
    decide

def quadrolaConic : Conic F₁₁ :=
  Quadrola.conic firstFocus secondFocus 8 associated_nonzero eight_nonzero

/-- The constructed quadrola coefficients are five times the very conic
which Exercise 15.16 claims is not a quadrola. -/
theorem coefficientScale :
    Quadrola.CoefficientScale quadrolaConic
      ExampleFifteenNine.printedConic 5 := by
  constructor <;>
    unfold quadrolaConic ExampleFifteenNine.printedConic Quadrola.conic
      Quadrola.conicD Quadrola.conicE Quadrola.conicF Quadrola.conicA
      Quadrola.conicB Quadrola.conicC firstFocus secondFocus <;>
    decide

/-- Exercise 15.16 is false as printed: the displayed `F₁₁` grammola is the
same conic proportion as this valid quadrola with associated quadrance eight. -/
theorem exercise_15_16_printed_counterexample :
    Quadrola.Presentation firstFocus secondFocus 8 ∧
      Quadrola.CoefficientScale quadrolaConic
        ExampleFifteenNine.printedConic 5 :=
  ⟨presentation, coefficientScale⟩

/-- The metric quadrola equation and the printed grammola equation therefore
have exactly the same finite locus. -/
theorem same_locus (point : Point F₁₁) :
    Quadrola.Contains firstFocus secondFocus 8 point ↔
      ExampleFifteenNine.printedConic.Contains point := by
  have definingEquation :
      Quadrola.Contains firstFocus secondFocus 8 point ↔
        quadrolaConic.Contains point := by
    unfold Quadrola.Contains Conic.Contains quadrolaConic
    rw [Quadrola.conic_evaluate]
  have coefficientLocus := conic_contains_iff_of_coefficient_scale
    quadrolaConic ExampleFifteenNine.printedConic 5 (by decide)
      coefficientScale.d coefficientScale.e coefficientScale.f
      coefficientScale.a coefficientScale.b coefficientScale.c point
  exact definingEquation.trans coefficientLocus

end ExerciseFifteenSixteen

namespace ExerciseFifteenSeventeen

/-- The two rationally displayed foci used for a quadrola whose quadratic
trace vanishes. -/
def firstFocus (K : Type*) [RFAP.ExplicitField K] : Point K := ⟨1, 0⟩

def secondFocus (K : Type*) [RFAP.ExplicitField K] : Point K := ⟨-1, 0⟩

theorem focus_quadrance :
    quadrance (firstFocus K) (secondFocus K) = 4 := by
  unfold quadrance firstFocus secondFocus
  ring1

private theorem four_nonzero (twoNonzero : (2 : K) ≠ 0) : (4 : K) ≠ 0 := by
  have fourAsProduct : (4 : K) = 2 * 2 := by ring1
  rw [fourAsProduct]
  exact RFAP.ExplicitField.mul_ne_zero twoNonzero twoNonzero

private theorem eight_nonzero (twoNonzero : (2 : K) ≠ 0) : (8 : K) ≠ 0 := by
  have eightAsProduct : (8 : K) = (2 * 2) * 2 := by ring1
  rw [eightAsProduct]
  exact RFAP.ExplicitField.mul_ne_zero
    (RFAP.ExplicitField.mul_ne_zero twoNonzero twoNonzero) twoNonzero

/-- The example has nonzero associated quadrance two and focal quadrance
four, so it is a valid quadrola over every constructive field outside
characteristic two. -/
theorem presentation (twoNonzero : (2 : K) ≠ 0) :
    Quadrola.Presentation (firstFocus K) (secondFocus K) 2 := by
  constructor
  · intro equal
    have xEqual := congrArg Point.x equal
    apply twoNonzero
    calc
      (2 : K) = 1 - (-1) := by ring1
      _ = (firstFocus K).x - (secondFocus K).x := by rfl
      _ = 0 := by rw [xEqual]; ring1
  · exact twoNonzero
  · rw [focus_quadrance]
    exact four_nonzero twoNonzero
  · intro equalQuadrance
    apply twoNonzero
    calc
      (2 : K) = 4 - 2 := by ring1
      _ = quadrance (firstFocus K) (secondFocus K) - 2 := by
        rw [focus_quadrance]
      _ = 0 := by rw [equalQuadrance]; ring1

def exampleConic [DecidableEq K] (twoNonzero : (2 : K) ≠ 0) : Conic K :=
  Quadrola.conic (firstFocus K) (secondFocus K) 2 twoNonzero
    (eight_nonzero twoNonzero)

/-- The example's two square coefficients are opposites. -/
theorem example_trace_zero [DecidableEq K]
    (twoNonzero : (2 : K) ≠ 0) :
    (exampleConic twoNonzero).d + (exampleConic twoNonzero).f = 0 := by
  unfold exampleConic Quadrola.conic Quadrola.conicD Quadrola.conicF
    firstFocus secondFocus
  ring1

/-- Exercise 15.17: the displayed quadrola cannot be proportional to any
grammola conic, in either coefficient-scale direction.  The proof uses only
the zero/nonzero quadratic-trace invariant. -/
theorem exercise_15_17 [DecidableEq K]
    (twoNonzero : (2 : K) ≠ 0) :
    Quadrola.Presentation (firstFocus K) (secondFocus K) 2 ∧
      ∀ (firstDiagonal secondDiagonal : Line K)
        (associatedQuadrance : K)
        (grammolaPresentation :
          Grammola.Presentation firstDiagonal secondDiagonal
            associatedQuadrance)
        (scale : K), scale ≠ 0 →
          (¬ Quadrola.CoefficientScale (exampleConic twoNonzero)
            (Grammola.conic firstDiagonal secondDiagonal
              grammolaPresentation.firstNonNull
              grammolaPresentation.secondNonNull associatedQuadrance
              twoNonzero) scale) ∧
          (¬ Quadrola.CoefficientScale
            (Grammola.conic firstDiagonal secondDiagonal
              grammolaPresentation.firstNonNull
              grammolaPresentation.secondNonNull associatedQuadrance
              twoNonzero) (exampleConic twoNonzero) scale) := by
  refine ⟨presentation twoNonzero, ?_⟩
  intro firstDiagonal secondDiagonal associatedQuadrance
    grammolaPresentation scale scaleNonzero
  let grammolaConic :=
    Grammola.conic firstDiagonal secondDiagonal
      grammolaPresentation.firstNonNull
      grammolaPresentation.secondNonNull associatedQuadrance twoNonzero
  have grammolaTraceNonzero : grammolaConic.d + grammolaConic.f ≠ 0 := by
    unfold grammolaConic
    exact Grammola.conic_trace_nonzero firstDiagonal secondDiagonal
      grammolaPresentation.firstNonNull
      grammolaPresentation.secondNonNull associatedQuadrance twoNonzero
  constructor
  · intro exampleScaled
    have scaledTrace :
        (exampleConic twoNonzero).d + (exampleConic twoNonzero).f =
          scale * (grammolaConic.d + grammolaConic.f) := by
      rw [exampleScaled.d, exampleScaled.f]
      ring1
    have scaledTraceNonzero :
        scale * (grammolaConic.d + grammolaConic.f) ≠ 0 :=
      RFAP.ExplicitField.mul_ne_zero scaleNonzero grammolaTraceNonzero
    apply scaledTraceNonzero
    calc
      scale * (grammolaConic.d + grammolaConic.f) =
          (exampleConic twoNonzero).d + (exampleConic twoNonzero).f :=
        scaledTrace.symm
      _ = 0 := example_trace_zero twoNonzero
  · intro grammolaScaled
    apply grammolaTraceNonzero
    calc
      grammolaConic.d + grammolaConic.f =
          scale *
            ((exampleConic twoNonzero).d + (exampleConic twoNonzero).f) := by
        rw [grammolaScaled.d, grammolaScaled.f]
        ring1
      _ = 0 := by rw [example_trace_zero]; ring1

end ExerciseFifteenSeventeen

end ChapterFifteenExamples

end DivineProportions
