import DivineProportions.Conics.Parabola
import DivineProportions.Isometries.Models
import DivineProportions.Trigonometry.Spread

/-!
# Divine Proportions, Chapter 19: tangent lines and conics

Translations, Taylor conics, and tangent lines are retained as explicit
finite coefficient records.  A non-singular point carries the disjunction
that one of the two displayed linear coefficients is nonzero, so every line
construction remains executable and choice-free.
-/

namespace DivineProportions

variable {K : Type*} [RFAP.ExplicitField K]

namespace Conic

/-- The coefficient record of the translate `τ_B(q)` from Theorem 118. -/
def translateConic (conic : Conic K) (offset : Point K) : Conic K where
  d := conic.d
  e := conic.e
  f := conic.f
  a := conic.a - 2 * conic.d * offset.x - conic.e * offset.y
  b := conic.b - 2 * conic.f * offset.y - conic.e * offset.x
  c := conic.d * offset.x ^ 2 + conic.e * offset.x * offset.y +
    conic.f * offset.y ^ 2 - conic.a * offset.x -
    conic.b * offset.y + conic.c
  quadratic_nonzero := conic.quadratic_nonzero

/-- The polynomial identity in the proof of Theorem 118. -/
theorem translateConic_evaluate
    (conic : Conic K) (offset point : Point K) :
    (translateConic conic offset).evaluate
        (translationPoint offset.x offset.y point) =
      conic.evaluate point := by
  unfold translateConic evaluate translationPoint
  ring1

/-- Theorem 118 (Translate of a conic): translation of a point transports
incidence to the explicitly translated conic, in both directions. -/
theorem translate_of_conic
    (conic : Conic K) (offset point : Point K) :
    conic.Contains point ↔
      (translateConic conic offset).Contains
        (translationPoint offset.x offset.y point) := by
  unfold Contains
  rw [translateConic_evaluate]

/-- Translation of a displayed line by `B`: its equation is obtained by
replacing `x,y` by `x-u,y-v`. -/
def translateLine (line : Line K) (offset : Point K) : Line K where
  a := line.a
  b := line.b
  c := line.c - line.a * offset.x - line.b * offset.y
  direction_nonzero := line.direction_nonzero

/-- Point incidence is transported by the displayed line translation. -/
theorem translateLine_contains_translationPoint
    (line : Line K) (offset point : Point K) :
    (translateLine line offset).Contains
        (translationPoint offset.x offset.y point) ↔
      line.Contains point := by
  unfold translateLine Line.Contains translationPoint
  constructor <;> intro equation
  · calc
      line.a * point.x + line.b * point.y + line.c =
          line.a * (point.x + offset.x) +
            line.b * (point.y + offset.y) +
            (line.c - line.a * offset.x - line.b * offset.y) := by ring1
      _ = 0 := equation
  · calc
      line.a * (point.x + offset.x) +
          line.b * (point.y + offset.y) +
          (line.c - line.a * offset.x - line.b * offset.y) =
        line.a * point.x + line.b * point.y + line.c := by ring1
      _ = 0 := equation

/-- The Taylor conic `q_A=τ_{-A}(q)`, which moves `A` to the origin. -/
def taylorConic (conic : Conic K) (point : Point K) : Conic K :=
  translateConic conic ⟨-point.x, -point.y⟩

/-- A conic is standard when it contains the origin. -/
def IsStandard (conic : Conic K) : Prop := conic.c = 0

/-- The two first-order coefficients at a displayed point. -/
def IsNonSingularAt (conic : Conic K) (point : Point K) : Prop :=
  conic.a + 2 * conic.d * point.x + conic.e * point.y ≠ 0 ∨
    conic.b + conic.e * point.x + 2 * conic.f * point.y ≠ 0

/-- A point on a conic moves to the origin of its standard Taylor conic. -/
theorem taylorConic_isStandard
    (conic : Conic K) (point : Point K) (onConic : conic.Contains point) :
    (taylorConic conic point).IsStandard := by
  unfold IsStandard taylorConic translateConic
  unfold Contains evaluate at onConic
  calc
    conic.d * (-point.x) ^ 2 +
          conic.e * (-point.x) * (-point.y) +
          conic.f * (-point.y) ^ 2 - conic.a * (-point.x) -
          conic.b * (-point.y) + conic.c =
      conic.d * point.x ^ 2 + conic.e * point.x * point.y +
        conic.f * point.y ^ 2 + conic.a * point.x +
        conic.b * point.y + conic.c := by ring1
    _ = 0 := onConic

/-- The linear coefficients of the Taylor conic are the two first-order
coefficients at the base point. -/
theorem taylorConic_linear_coefficients
    (conic : Conic K) (point : Point K) :
    (taylorConic conic point).a =
        conic.a + 2 * conic.d * point.x + conic.e * point.y ∧
      (taylorConic conic point).b =
        conic.b + conic.e * point.x + 2 * conic.f * point.y := by
  unfold taylorConic translateConic
  constructor <;> ring1

/-- Non-singularity at `A` is exactly non-singularity of the linear part of
the Taylor conic at the origin. -/
theorem taylorConic_linear_nonzero
    (conic : Conic K) (point : Point K)
    (nonSingular : conic.IsNonSingularAt point) :
    (taylorConic conic point).a ≠ 0 ∨
      (taylorConic conic point).b ≠ 0 := by
  rw [taylorConic_linear_coefficients conic point |>.1,
    taylorConic_linear_coefficients conic point |>.2]
  exact nonSingular

/-- The tangent at the origin of a non-singular standard conic is its linear
part. -/
def standardTangentAtOrigin
    (conic : Conic K) (linearNonzero : conic.a ≠ 0 ∨ conic.b ≠ 0) :
    Line K where
  a := conic.a
  b := conic.b
  c := 0
  direction_nonzero := linearNonzero

/-- The explicit tangent-line representative printed in Theorem 119. -/
def tangentLine
    (conic : Conic K) (point : Point K)
    (nonSingular : conic.IsNonSingularAt point) : Line K where
  a := conic.a + 2 * conic.d * point.x + conic.e * point.y
  b := conic.b + conic.e * point.x + 2 * conic.f * point.y
  c := conic.a * point.x + conic.b * point.y + 2 * conic.c
  direction_nonzero := nonSingular

/-- The tangent formula always passes through its base point once the point
lies on the conic. -/
theorem tangentLine_contains
    (conic : Conic K) (point : Point K)
    (onConic : conic.Contains point)
    (nonSingular : conic.IsNonSingularAt point) :
    (tangentLine conic point nonSingular).Contains point := by
  unfold tangentLine Line.Contains
  unfold Contains evaluate at onConic
  calc
    (conic.a + 2 * conic.d * point.x + conic.e * point.y) * point.x +
        (conic.b + conic.e * point.x + 2 * conic.f * point.y) * point.y +
        (conic.a * point.x + conic.b * point.y + 2 * conic.c) =
      2 * (conic.d * point.x ^ 2 +
        conic.e * point.x * point.y + conic.f * point.y ^ 2 +
        conic.a * point.x + conic.b * point.y + conic.c) := by ring1
    _ = 0 := by rw [onConic]; ring1

/-- Theorem 119 (Tangent to a conic): translating the linear part of the
Taylor conic back to `A` gives the printed tangent representative, up to the
source's line proportion, and that representative contains `A`. -/
theorem tangent_to_conic
    (conic : Conic K) (point : Point K)
    (onConic : conic.Contains point)
    (nonSingular : conic.IsNonSingularAt point) :
    (translateLine
        (standardTangentAtOrigin (taylorConic conic point)
          (taylorConic_linear_nonzero conic point nonSingular))
        point).Equivalent
      (tangentLine conic point nonSingular) ∧
    (tangentLine conic point nonSingular).Contains point := by
  constructor
  · unfold Line.Equivalent
    dsimp only [translateLine, standardTangentAtOrigin, tangentLine,
      taylorConic, translateConic]
    unfold Contains evaluate at onConic
    have tangentConstant :
        conic.a * point.x + conic.b * point.y + 2 * conic.c =
          -(conic.a + 2 * conic.d * point.x + conic.e * point.y) *
              point.x -
            (conic.b + 2 * conic.f * point.y + conic.e * point.x) *
              point.y := by
      calc
        conic.a * point.x + conic.b * point.y + 2 * conic.c =
            -(conic.a + 2 * conic.d * point.x +
                conic.e * point.y) * point.x -
              (conic.b + 2 * conic.f * point.y +
                conic.e * point.x) * point.y +
              2 * (conic.d * point.x ^ 2 +
                conic.e * point.x * point.y +
                conic.f * point.y ^ 2 + conic.a * point.x +
                conic.b * point.y + conic.c) := by ring1
        _ = _ := by rw [onConic]; ring1
    rw [tangentConstant]
    exact ⟨by ring1, by ring1, by ring1⟩
  · exact tangentLine_contains conic point onConic nonSingular

private theorem eq_zero_of_mul_eq_zero_left
    {factor value : K} (factorNonzero : factor ≠ 0)
    (productZero : factor * value = 0) : value = 0 := by
  have inverseCancel : factor⁻¹ * factor = (1 : K) := by
    calc
      factor⁻¹ * factor = factor * factor⁻¹ := by ring1
      _ = 1 := RFAP.ExplicitField.mul_inv_cancel factor factorNonzero
  calc
    value = 1 * value := by ring1
    _ = (factor⁻¹ * factor) * value := by rw [inverseCancel]
    _ = factor⁻¹ * (factor * value) := by ring1
    _ = 0 := by rw [productZero]; ring1

/-- Theorem 120 (Tangent to a circle): at every point of a circle with
nonzero quadrance, the explicit tangent is non-singular, non-null, and is the
altitude from the point to the line joining it to the center. -/
theorem tangent_to_circle
    [Nontrivial K] [DecidableEq K]
    (conic : Conic K) (center point : Point K) (circleQuadrance : K)
    (presentation :
      conic.IsCirclePresentation center circleQuadrance)
    (onCircle : conic.Contains point)
    (twoNonzero : (2 : K) ≠ 0)
    (quadranceNonzero : circleQuadrance ≠ 0) :
    ∃ pointCenterDistinct : point ≠ center,
      ∃ nonSingular : conic.IsNonSingularAt point,
        let tangent := tangentLine conic point nonSingular
        let centerLine := lineThrough point center pointCenterDistinct
        tangent.Contains point ∧
          ¬ tangent.IsNull ∧
          tangent.Perpendicular centerLine ∧
          tangent.Equivalent (altitudeThrough point centerLine) := by
  have pointQuadrance : quadrance point center = circleQuadrance :=
    (contains_iff_quadrance_eq conic center point circleQuadrance
      presentation).1 onCircle
  have pointCenterDistinct : point ≠ center := by
    intro equalPoints
    apply quadranceNonzero
    calc
      circleQuadrance = quadrance point center := pointQuadrance.symm
      _ = quadrance center center := by rw [equalPoints]
      _ = 0 := quadrance_self center
  have eZero := presentation.1
  have dEqualsF := presentation.2.1
  have dNonzero := presentation.2.2.1
  have aFormula := presentation.2.2.2.1
  have bFormula := presentation.2.2.2.2.1
  let scale := 2 * conic.d
  have scaleNonzero : scale ≠ 0 :=
    RFAP.ExplicitField.mul_ne_zero twoNonzero dNonzero
  have gradientX :
      conic.a + 2 * conic.d * point.x + conic.e * point.y =
        scale * (point.x - center.x) := by
    rw [eZero, aFormula]
    unfold scale
    ring1
  have gradientY :
      conic.b + conic.e * point.x + 2 * conic.f * point.y =
        scale * (point.y - center.y) := by
    rw [eZero, ← dEqualsF, bFormula]
    unfold scale
    ring1
  have nonSingular : conic.IsNonSingularAt point := by
    unfold IsNonSingularAt
    by_cases firstNonzero :
        conic.a + 2 * conic.d * point.x + conic.e * point.y ≠ 0
    · exact Or.inl firstNonzero
    · right
      intro secondZero
      have xDifferenceZero : point.x - center.x = 0 :=
        eq_zero_of_mul_eq_zero_left scaleNonzero (by
          rw [← gradientX]
          by_cases firstZero :
              conic.a + 2 * conic.d * point.x +
                conic.e * point.y = 0
          · exact firstZero
          · exact False.elim (firstNonzero firstZero))
      have yDifferenceZero : point.y - center.y = 0 :=
        eq_zero_of_mul_eq_zero_left scaleNonzero (by
          rw [← gradientY]
          exact secondZero)
      apply pointCenterDistinct
      apply Point.ext
      · calc
          point.x = (point.x - center.x) + center.x := by ring1
          _ = center.x := by rw [xDifferenceZero]; ring1
      · calc
          point.y = (point.y - center.y) + center.y := by ring1
          _ = center.y := by rw [yDifferenceZero]; ring1
  refine ⟨pointCenterDistinct, nonSingular, ?_⟩
  dsimp only
  let tangent := tangentLine conic point nonSingular
  let centerLine := lineThrough point center pointCenterDistinct
  let altitude := altitudeThrough point centerLine
  have tangentContains : tangent.Contains point :=
    tangentLine_contains conic point onCircle nonSingular
  have tangentA : tangent.a = scale * altitude.a := by
    change conic.a + 2 * conic.d * point.x + conic.e * point.y =
      scale * (-(center.x - point.x))
    rw [gradientX]
    ring1
  have tangentB : tangent.b = scale * altitude.b := by
    change conic.b + conic.e * point.x + 2 * conic.f * point.y =
      scale * (point.y - center.y)
    exact gradientY
  have tangentConstantFromIncidence :
      tangent.c = -tangent.a * point.x - tangent.b * point.y := by
    unfold Line.Contains at tangentContains
    calc
      tangent.c =
          (tangent.a * point.x + tangent.b * point.y + tangent.c) -
            tangent.a * point.x - tangent.b * point.y := by ring1
      _ = -tangent.a * point.x - tangent.b * point.y := by
        rw [tangentContains]
        ring1
  have tangentC : tangent.c = scale * altitude.c := by
    rw [tangentConstantFromIncidence, tangentA, tangentB]
    change
      -(scale * (-(center.x - point.x))) * point.x -
          scale * (point.y - center.y) * point.y =
        scale * ((center.x - point.x) * point.x -
          (point.y - center.y) * point.y)
    ring1
  have tangentNonNull : ¬ tangent.IsNull := by
    intro tangentNull
    have scaledQuadranceZero :
        (scale * scale) * quadrance point center = 0 := by
      calc
        (scale * scale) * quadrance point center =
            tangent.a ^ 2 + tangent.b ^ 2 := by
          rw [tangentA, tangentB]
          unfold altitude centerLine altitudeThrough lineThrough quadrance
          ring1
        _ = 0 := tangentNull
    have scaledQuadranceNonzero :
        (scale * scale) * quadrance point center ≠ 0 :=
      RFAP.ExplicitField.mul_ne_zero
        (RFAP.ExplicitField.mul_ne_zero scaleNonzero scaleNonzero)
        (by rw [pointQuadrance]; exact quadranceNonzero)
    exact scaledQuadranceNonzero scaledQuadranceZero
  have tangentPerpendicular : tangent.Perpendicular centerLine := by
    unfold Line.Perpendicular
    rw [tangentA, tangentB]
    unfold altitude centerLine altitudeThrough lineThrough
    ring1
  have tangentEquivalentAltitude : tangent.Equivalent altitude := by
    unfold Line.Equivalent
    rw [tangentA, tangentB, tangentC]
    exact ⟨by ring1, by ring1, by ring1⟩
  exact ⟨tangentContains, tangentNonNull, tangentPerpendicular,
    tangentEquivalentAltitude⟩

/-- Evaluation through an arbitrary scaled focus/directrix presentation. -/
theorem evaluate_eq_scale_mul_parabola_residual
    (conic : Conic K) (focus point : Point K) (directrix : Line K)
    (presentation :
      ParabolaPresentationData conic focus directrix) :
    conic.evaluate point = presentation.scale *
      (lineNorm directrix * quadrance point focus -
        (directrix.a * point.x + directrix.b * point.y +
          directrix.c) ^ 2) := by
  unfold evaluate lineNorm quadrance
  rw [presentation.dEquation, presentation.eEquation,
    presentation.fEquation, presentation.aEquation,
    presentation.bEquation, presentation.cEquation]
  unfold lineNorm
  ring1

/-- Incidence with a presented parabola is the denominator-cleared equality
between focus quadrance and squared directrix evaluation. -/
theorem parabola_incidence_residual
    (conic : Conic K) (focus point : Point K) (directrix : Line K)
    (presentation :
      ParabolaPresentationData conic focus directrix)
    (onParabola : conic.Contains point) :
    lineNorm directrix * quadrance point focus =
      (directrix.a * point.x + directrix.b * point.y +
        directrix.c) ^ 2 := by
  have scaledResidualZero : presentation.scale *
      (lineNorm directrix * quadrance point focus -
        (directrix.a * point.x + directrix.b * point.y +
          directrix.c) ^ 2) = 0 := by
    calc
      presentation.scale *
          (lineNorm directrix * quadrance point focus -
            (directrix.a * point.x + directrix.b * point.y +
              directrix.c) ^ 2) = conic.evaluate point :=
        (evaluate_eq_scale_mul_parabola_residual conic focus point
          directrix presentation).symm
      _ = 0 := onParabola
  have residualZero := eq_zero_of_mul_eq_zero_left
    presentation.scaleNonzero scaledResidualZero
  exact sub_eq_zero.mp residualZero

/-- A point of a valid focus/directrix parabola cannot be its focus. -/
theorem parabola_point_ne_focus
    [DecidableEq K]
    (conic : Conic K) (focus point : Point K) (directrix : Line K)
    (presentation : conic.IsParabolaPresentation focus directrix)
    (onParabola : conic.Contains point) : point ≠ focus := by
  rcases presentation with ⟨presentation⟩
  intro pointEqualsFocus
  have residual := parabola_incidence_residual conic focus point directrix
    presentation onParabola
  have focusEvaluationSquaredZero :
      (directrix.a * focus.x + directrix.b * focus.y +
        directrix.c) ^ 2 = 0 := by
    rw [pointEqualsFocus] at residual
    calc
      (directrix.a * focus.x + directrix.b * focus.y +
          directrix.c) ^ 2 =
        lineNorm directrix * quadrance focus focus := residual.symm
      _ = 0 := by rw [quadrance_self]; ring1
  have focusEvaluationZero :
      directrix.a * focus.x + directrix.b * focus.y +
        directrix.c = 0 := by
    by_cases evaluationZero :
        directrix.a * focus.x + directrix.b * focus.y +
          directrix.c = 0
    · exact evaluationZero
    · exact False.elim
        ((RFAP.ExplicitField.mul_ne_zero evaluationZero evaluationZero)
          (by simpa only [pow_two] using focusEvaluationSquaredZero))
  apply presentation.focusNotOnDirectrix
  exact focusEvaluationZero

/-- Every point of a valid parabola is first-order non-singular once two is
nonzero.  The proof combines the two gradient coordinates into the nonzero
focus/directrix separation. -/
theorem parabola_nonSingularAt
    [DecidableEq K]
    (conic : Conic K) (focus point : Point K) (directrix : Line K)
    (twoNonzero : (2 : K) ≠ 0)
    (presentation : conic.IsParabolaPresentation focus directrix) :
    conic.IsNonSingularAt point := by
  rcases presentation with ⟨presentation⟩
  let gradientX :=
    conic.a + 2 * conic.d * point.x + conic.e * point.y
  let gradientY :=
    conic.b + conic.e * point.x + 2 * conic.f * point.y
  let focusEvaluation :=
    directrix.a * focus.x + directrix.b * focus.y + directrix.c
  have normNonzero : lineNorm directrix ≠ 0 :=
    presentation.directrixNonNull
  have focusEvaluationNonzero : focusEvaluation ≠ 0 := by
    intro evaluationZero
    apply presentation.focusNotOnDirectrix
    exact evaluationZero
  have combinedGradient :
      directrix.a * gradientX + directrix.b * gradientY =
        -(presentation.scale * 2 * lineNorm directrix *
          focusEvaluation) := by
    unfold gradientX gradientY focusEvaluation lineNorm
    rw [presentation.dEquation, presentation.eEquation,
      presentation.fEquation, presentation.aEquation,
      presentation.bEquation]
    unfold lineNorm
    ring1
  have combinedGradientNonzero :
      directrix.a * gradientX + directrix.b * gradientY ≠ 0 := by
    rw [combinedGradient]
    intro negativeProductZero
    have productZero :
        presentation.scale * 2 * lineNorm directrix *
          focusEvaluation = 0 := by
      calc
        presentation.scale * 2 * lineNorm directrix * focusEvaluation =
            -(-(presentation.scale * 2 * lineNorm directrix *
              focusEvaluation)) := by ring1
        _ = 0 := by rw [negativeProductZero]; ring1
    exact (RFAP.ExplicitField.mul_ne_zero
      (RFAP.ExplicitField.mul_ne_zero
        (RFAP.ExplicitField.mul_ne_zero presentation.scaleNonzero
          twoNonzero) normNonzero) focusEvaluationNonzero) productZero
  unfold IsNonSingularAt
  change gradientX ≠ 0 ∨ gradientY ≠ 0
  by_cases firstNonzero : gradientX ≠ 0
  · exact Or.inl firstNonzero
  · right
    intro secondZero
    have firstZero : gradientX = 0 := by
      by_cases zero : gradientX = 0
      · exact zero
      · exact False.elim (firstNonzero zero)
    apply combinedGradientNonzero
    rw [firstZero, secondZero]
    ring1

/-- The altitude to a non-null line is itself non-null. -/
theorem altitudeThrough_nonNull
    (point : Point K) (line : Line K) (lineNonNull : ¬ line.IsNull) :
    ¬ (altitudeThrough point line).IsNull := by
  intro altitudeNull
  apply lineNonNull
  unfold Line.IsNull at altitudeNull ⊢
  unfold altitudeThrough at altitudeNull
  calc
    line.a ^ 2 + line.b ^ 2 =
        (-line.b) ^ 2 + line.a ^ 2 := by ring1
    _ = 0 := altitudeNull

private theorem div_eq_div_of_cross_mul
    {leftNumerator rightNumerator leftDenominator rightDenominator : K}
    (leftNonzero : leftDenominator ≠ 0)
    (rightNonzero : rightDenominator ≠ 0)
    (crossProduct :
      leftNumerator * rightDenominator =
        rightNumerator * leftDenominator) :
    leftNumerator / leftDenominator =
      rightNumerator / rightDenominator := by
  have leftCancel : leftDenominator * leftDenominator⁻¹ = (1 : K) :=
    RFAP.ExplicitField.mul_inv_cancel leftDenominator leftNonzero
  have rightCancel : rightDenominator * rightDenominator⁻¹ = (1 : K) :=
    RFAP.ExplicitField.mul_inv_cancel rightDenominator rightNonzero
  simp only [RFAP.ExplicitField.div_eq_mul_inv]
  calc
    leftNumerator * leftDenominator⁻¹ =
        leftNumerator * leftDenominator⁻¹ *
          (rightDenominator * rightDenominator⁻¹) := by
      rw [rightCancel]
      ring1
    _ = (leftNumerator * rightDenominator) *
        (leftDenominator⁻¹ * rightDenominator⁻¹) := by ring1
    _ = (rightNumerator * leftDenominator) *
        (leftDenominator⁻¹ * rightDenominator⁻¹) := by
      rw [crossProduct]
    _ = rightNumerator *
        (leftDenominator * leftDenominator⁻¹) *
          rightDenominator⁻¹ := by ring1
    _ = rightNumerator * rightDenominator⁻¹ := by
      rw [leftCancel]
      ring1

/-- Theorem 121 (Parabola reflection): the tangent at a point of a presented
parabola makes equal spreads with the focus line and the altitude to the
directrix.  The source's implicit requirement that `AF` be non-null is exposed
because otherwise its displayed spread is undefined. -/
theorem parabola_reflection
    [DecidableEq K]
    (conic : Conic K) (focus point : Point K) (directrix : Line K)
    (twoNonzero : (2 : K) ≠ 0)
    (presentation : conic.IsParabolaPresentation focus directrix)
    (onParabola : conic.Contains point)
    (focusLineNonNull :
      ¬ (lineThrough point focus
        (parabola_point_ne_focus conic focus point directrix presentation
          onParabola)).IsNull) :
    let pointFocusDistinct :=
      parabola_point_ne_focus conic focus point directrix presentation
        onParabola
    let nonSingular :=
      parabola_nonSingularAt conic focus point directrix twoNonzero
        presentation
    let tangent := tangentLine conic point nonSingular
    let focusLine := lineThrough point focus pointFocusDistinct
    let normalLine := altitudeThrough point directrix
    ∃ tangentNonNull : ¬ tangent.IsNull,
      ∃ normalLineNonNull : ¬ normalLine.IsNull,
        spread tangent focusLine tangentNonNull focusLineNonNull =
          spread tangent normalLine tangentNonNull normalLineNonNull := by
  dsimp only
  let pointFocusDistinct :=
    parabola_point_ne_focus conic focus point directrix presentation
      onParabola
  let nonSingular :=
    parabola_nonSingularAt conic focus point directrix twoNonzero
      presentation
  let tangent := tangentLine conic point nonSingular
  let focusLine := lineThrough point focus pointFocusDistinct
  let normalLine := altitudeThrough point directrix
  rcases presentation with ⟨presentation⟩
  let norm := lineNorm directrix
  let evaluation :=
    directrix.a * point.x + directrix.b * point.y + directrix.c
  let focusEvaluation :=
    directrix.a * focus.x + directrix.b * focus.y + directrix.c
  let scaleTwo := presentation.scale * 2
  have normNonzero : norm ≠ 0 := presentation.directrixNonNull
  have focusEvaluationNonzero : focusEvaluation ≠ 0 := by
    intro evaluationZero
    apply presentation.focusNotOnDirectrix
    exact evaluationZero
  have parabolaEquation :
      norm * quadrance point focus = evaluation ^ 2 := by
    exact parabola_incidence_residual conic focus point directrix
      presentation onParabola
  have focusLineNorm : lineNorm focusLine = quadrance point focus := by
    unfold focusLine lineNorm lineThrough quadrance
    ring1
  have focusQuadranceNonzero : quadrance point focus ≠ 0 := by
    intro quadranceZero
    apply focusLineNonNull
    change lineNorm focusLine = 0
    rw [focusLineNorm, quadranceZero]
  have evaluationNonzero : evaluation ≠ 0 := by
    intro evaluationZero
    have productZero : norm * quadrance point focus = 0 := by
      rw [parabolaEquation, evaluationZero]
      ring1
    exact (RFAP.ExplicitField.mul_ne_zero normNonzero
      focusQuadranceNonzero) productZero
  have scaleTwoNonzero : scaleTwo ≠ 0 :=
    RFAP.ExplicitField.mul_ne_zero presentation.scaleNonzero twoNonzero
  have tangentA : tangent.a = scaleTwo *
      (norm * (point.x - focus.x) - directrix.a * evaluation) := by
    change conic.a + 2 * conic.d * point.x + conic.e * point.y = _
    rw [presentation.aEquation, presentation.dEquation,
      presentation.eEquation]
    unfold scaleTwo norm evaluation lineNorm
    ring1
  have tangentB : tangent.b = scaleTwo *
      (norm * (point.y - focus.y) - directrix.b * evaluation) := by
    change conic.b + conic.e * point.x + 2 * conic.f * point.y = _
    rw [presentation.bEquation, presentation.eEquation,
      presentation.fEquation]
    unfold scaleTwo norm evaluation lineNorm
    ring1
  have baseTangentNorm :
      (norm * (point.x - focus.x) - directrix.a * evaluation) ^ 2 +
          (norm * (point.y - focus.y) - directrix.b * evaluation) ^ 2 =
        2 * norm * evaluation * focusEvaluation := by
    calc
      (norm * (point.x - focus.x) - directrix.a * evaluation) ^ 2 +
            (norm * (point.y - focus.y) - directrix.b * evaluation) ^ 2 =
          norm * (norm * quadrance point focus -
            2 * evaluation *
              (directrix.a * (point.x - focus.x) +
                directrix.b * (point.y - focus.y)) +
            evaluation ^ 2) := by
        unfold norm lineNorm quadrance
        ring1
      _ = norm * (evaluation ^ 2 -
            2 * evaluation *
              (directrix.a * (point.x - focus.x) +
                directrix.b * (point.y - focus.y)) +
            evaluation ^ 2) := by
        rw [parabolaEquation]
      _ = 2 * norm * evaluation * focusEvaluation := by
        unfold evaluation focusEvaluation
        ring1
  have tangentNorm :
      lineNorm tangent =
        (scaleTwo * scaleTwo) *
          (2 * norm * evaluation * focusEvaluation) := by
    unfold lineNorm
    rw [tangentA, tangentB]
    calc
      (scaleTwo *
              (norm * (point.x - focus.x) -
                directrix.a * evaluation)) ^ 2 +
          (scaleTwo *
              (norm * (point.y - focus.y) -
                directrix.b * evaluation)) ^ 2 =
        (scaleTwo * scaleTwo) *
          ((norm * (point.x - focus.x) -
              directrix.a * evaluation) ^ 2 +
            (norm * (point.y - focus.y) -
              directrix.b * evaluation) ^ 2) := by ring1
      _ = (scaleTwo * scaleTwo) *
          (2 * norm * evaluation * focusEvaluation) := by
        rw [baseTangentNorm]
  have baseNormNonzero :
      2 * norm * evaluation * focusEvaluation ≠ 0 :=
    RFAP.ExplicitField.mul_ne_zero
      (RFAP.ExplicitField.mul_ne_zero
        (RFAP.ExplicitField.mul_ne_zero twoNonzero normNonzero)
        evaluationNonzero) focusEvaluationNonzero
  have tangentNonNull : ¬ tangent.IsNull := by
    intro tangentNull
    have tangentNormZero : lineNorm tangent = 0 := tangentNull
    have displayedProductZero :
        (scaleTwo * scaleTwo) *
          (2 * norm * evaluation * focusEvaluation) = 0 := by
      rw [← tangentNorm]
      exact tangentNormZero
    exact (RFAP.ExplicitField.mul_ne_zero
      (RFAP.ExplicitField.mul_ne_zero scaleTwoNonzero scaleTwoNonzero)
      baseNormNonzero) displayedProductZero
  have normalLineNonNull : ¬ normalLine.IsNull :=
    altitudeThrough_nonNull point directrix presentation.directrixNonNull
  have normalLineNorm : lineNorm normalLine = norm := by
    unfold normalLine altitudeThrough norm
    unfold lineNorm
    ring1
  have focusDeterminant :
      tangent.a * focusLine.b - focusLine.a * tangent.b =
        -(scaleTwo * evaluation * focusEvaluation) := by
    rw [tangentA, tangentB]
    unfold focusLine lineThrough
    calc
      scaleTwo *
              (norm * (point.x - focus.x) - directrix.a * evaluation) *
            (focus.x - point.x) -
          (point.y - focus.y) *
            (scaleTwo *
              (norm * (point.y - focus.y) - directrix.b * evaluation)) =
        -(scaleTwo *
          (norm * quadrance point focus - evaluation *
            (directrix.a * (point.x - focus.x) +
              directrix.b * (point.y - focus.y)))) := by
        unfold quadrance
        ring1
      _ = -(scaleTwo *
          (evaluation ^ 2 - evaluation *
            (directrix.a * (point.x - focus.x) +
              directrix.b * (point.y - focus.y)))) := by
        rw [parabolaEquation]
      _ = -(scaleTwo * evaluation * focusEvaluation) := by
        unfold evaluation focusEvaluation
        ring1
  have normalDeterminant :
      tangent.a * normalLine.b - normalLine.a * tangent.b =
        -(scaleTwo * norm * focusEvaluation) := by
    rw [tangentA, tangentB]
    unfold normalLine altitudeThrough
    unfold norm evaluation focusEvaluation
    unfold lineNorm
    ring1
  have focusLineNormExpanded :
      focusLine.a ^ 2 + focusLine.b ^ 2 = quadrance point focus :=
    focusLineNorm
  have normalLineNormExpanded :
      normalLine.a ^ 2 + normalLine.b ^ 2 = norm :=
    normalLineNorm
  refine ⟨tangentNonNull, normalLineNonNull, ?_⟩
  change
    (tangent.a * focusLine.b - focusLine.a * tangent.b) ^ 2 /
        (lineNorm tangent * lineNorm focusLine) =
      (tangent.a * normalLine.b - normalLine.a * tangent.b) ^ 2 /
        (lineNorm tangent * lineNorm normalLine)
  apply div_eq_div_of_cross_mul
    (RFAP.ExplicitField.mul_ne_zero tangentNonNull focusLineNonNull)
    (RFAP.ExplicitField.mul_ne_zero tangentNonNull normalLineNonNull)
  rw [focusDeterminant, normalDeterminant, focusLineNormExpanded,
    normalLineNormExpanded]
  calc
    (-(scaleTwo * evaluation * focusEvaluation)) ^ 2 *
          ((tangent.a ^ 2 + tangent.b ^ 2) * norm) =
        scaleTwo ^ 2 * focusEvaluation ^ 2 *
          (tangent.a ^ 2 + tangent.b ^ 2) * norm * evaluation ^ 2 := by
      ring1
    _ = scaleTwo ^ 2 * focusEvaluation ^ 2 *
          (tangent.a ^ 2 + tangent.b ^ 2) * norm *
            (norm * quadrance point focus) := by
      rw [← parabolaEquation]
    _ = (-(scaleTwo * norm * focusEvaluation)) ^ 2 *
          ((tangent.a ^ 2 + tangent.b ^ 2) *
            quadrance point focus) := by
      ring1

end Conic

end DivineProportions
