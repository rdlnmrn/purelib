import DivineProportions.Conics.Tangent

/-!
# Divine Proportions, Chapter 19 worked examples

This module begins with the translated-conic and tangent-line calculations in
Examples 19.1--19.4, then records the exact two-tangent identity and its
eleven-element-field instance from Exercise 19.2.
-/

namespace DivineProportions

namespace ChapterNineteenExamples

variable {K : Type*} [RFAP.ExplicitField K]

namespace ExampleNineteenOne

/-- The unit circle `⟨1:0:1:0:0:-1⟩` from Example 19.1. -/
def circle [Nontrivial K] : Conic K :=
  Conic.circleConic ⟨0, 0⟩ 1

/-- The displayed translation vector `[2,3]`. -/
def offset : Point K := ⟨2, 3⟩

/-- Example 19.1: translating the unit circle by `[2,3]` gives the expanded
equation `(x-2)²+(y-3)²-1=0`. -/
theorem example_19_1 [Nontrivial K] :
    let translated := Conic.translateConic (circle (K := K)) (offset (K := K))
    translated.d = 1 ∧ translated.e = 0 ∧ translated.f = 1 ∧
      translated.a = -4 ∧ translated.b = -6 ∧ translated.c = 12 ∧
      ∀ point : Point K,
        translated.evaluate point =
          (point.x - 2) ^ 2 + (point.y - 3) ^ 2 - 1 := by
  dsimp only [circle, offset, Conic.circleConic, Conic.translateConic]
  refine ⟨by ring1, by ring1, by ring1, by ring1, by ring1, by ring1, ?_⟩
  intro point
  unfold Conic.evaluate
  ring1

end ExampleNineteenOne

namespace ExampleNineteenTwo

/-- The conic `⟨1:-2:-1:1:0:-5⟩` in Examples 19.2 and 19.3. -/
def conic [Nontrivial K] : Conic K where
  d := 1
  e := -2
  f := -1
  a := 1
  b := 0
  c := -5
  quadratic_nonzero := Or.inl one_ne_zero

/-- The displayed point `[3,1]`. -/
def point : Point K := ⟨3, 1⟩

/-- Example 19.2: `[3,1]` lies on the conic and its Taylor conic is
`⟨1:-2:-1:5:-8:0⟩`. -/
theorem example_19_2 [Nontrivial K] :
    let source := conic (K := K)
    let basePoint := point (K := K)
    let taylor := Conic.taylorConic source basePoint
    source.Contains basePoint ∧
      taylor.d = 1 ∧ taylor.e = -2 ∧ taylor.f = -1 ∧
      taylor.a = 5 ∧ taylor.b = -8 ∧ taylor.c = 0 := by
  dsimp only [conic, point, Conic.taylorConic, Conic.translateConic,
    Conic.Contains, Conic.evaluate]
  exact ⟨by ring1, by ring1, by ring1, by ring1, by ring1, by ring1,
    by ring1⟩

/-- Example 19.3: the printed tangent representative at `[3,1]` is
`⟨5:-8:-7⟩`.  Its required non-singularity is supplied as the exact
disjunction between the two displayed linear coefficients. -/
theorem example_19_3 [Nontrivial K]
    (linearNonzero : (5 : K) ≠ 0 ∨ (-8 : K) ≠ 0) :
    let source := conic (K := K)
    let basePoint := point (K := K)
    let nonSingular : source.IsNonSingularAt basePoint := by
      unfold Conic.IsNonSingularAt source basePoint conic point
      have firstValue : (1 + 2 * 1 * 3 + -2 * 1 : K) = 5 := by ring1
      have secondValue : (0 + -2 * 3 + 2 * -1 * 1 : K) = -8 := by ring1
      rw [firstValue, secondValue]
      exact linearNonzero
    let tangent := Conic.tangentLine source basePoint nonSingular
    tangent.a = 5 ∧ tangent.b = -8 ∧ tangent.c = -7 ∧
      tangent.Contains basePoint := by
  dsimp only
  let source := conic (K := K)
  let basePoint := point (K := K)
  have onConic : source.Contains basePoint := by
    unfold source basePoint conic point Conic.Contains Conic.evaluate
    ring1
  have nonSingular : source.IsNonSingularAt basePoint := by
    unfold source basePoint conic point Conic.IsNonSingularAt
    simpa only [show (1 + 2 * 1 * 3 + -2 * 1 : K) = 5 by ring1,
      show (0 + -2 * 3 + 2 * -1 * 1 : K) = -8 by ring1] using
      linearNonzero
  refine ⟨?_, ?_, ?_, Conic.tangentLine_contains source basePoint onConic
    nonSingular⟩
  · change (1 : K) + 2 * 1 * 3 + -2 * 1 = 5
    ring1
  · change (0 : K) + -2 * 3 + 2 * -1 * 1 = -8
    ring1
  · change (1 : K) * 3 + 0 * 1 + 2 * -5 = -7
    ring1

end ExampleNineteenTwo

namespace ExampleNineteenFour

/-- The parabola `y²=4x`, displayed as `⟨0:0:1:-4:0:0⟩`. -/
def parabola [Nontrivial K] : Conic K where
  d := 0
  e := 0
  f := 1
  a := -4
  b := 0
  c := 0
  quadratic_nonzero := Or.inr (Or.inr one_ne_zero)

/-- The book's parametrized point `[t²,2t]`. -/
def point (parameter : K) : Point K :=
  ⟨parameter ^ 2, 2 * parameter⟩

/-- The normalized tangent representative `⟨1:-t:t²⟩`. -/
def normalizedTangent [Nontrivial K] (parameter : K) : Line K where
  a := 1
  b := -parameter
  c := parameter ^ 2
  direction_nonzero := Or.inl one_ne_zero

private theorem negative_four_nonzero (fourNonzero : (4 : K) ≠ 0) :
    (-4 : K) ≠ 0 := by
  intro negativeZero
  apply fourNonzero
  calc
    (4 : K) = -(-4) := by ring1
    _ = 0 := by rw [negativeZero]; ring1

/-- Example 19.4: every displayed parameter point lies on `y²=4x`; the
tangent formula is proportional to `⟨1:-t:t²⟩`. -/
theorem example_19_4 [Nontrivial K]
    (parameter : K) (fourNonzero : (4 : K) ≠ 0) :
    let source := parabola (K := K)
    let basePoint := point parameter
    let nonSingular : source.IsNonSingularAt basePoint := by
      unfold Conic.IsNonSingularAt source basePoint parabola point
      left
      intro gradientZero
      apply negative_four_nonzero fourNonzero
      calc
        (-4 : K) = -4 + 2 * 0 * parameter ^ 2 + 0 * (2 * parameter) := by
          ring1
        _ = 0 := gradientZero
    let tangent := Conic.tangentLine source basePoint nonSingular
    source.Contains basePoint ∧
      tangent.Equivalent (normalizedTangent parameter) ∧
      tangent.Contains basePoint := by
  dsimp only
  let source := parabola (K := K)
  let basePoint := point parameter
  have onParabola : source.Contains basePoint := by
    unfold source basePoint parabola point Conic.Contains Conic.evaluate
    ring1
  have nonSingular : source.IsNonSingularAt basePoint := by
    unfold source basePoint parabola point Conic.IsNonSingularAt
    left
    intro gradientZero
    apply negative_four_nonzero fourNonzero
    calc
      (-4 : K) = -4 + 2 * 0 * parameter ^ 2 + 0 * (2 * parameter) := by
        ring1
      _ = 0 := gradientZero
  let tangent := Conic.tangentLine source basePoint nonSingular
  have tangentEquivalent : tangent.Equivalent (normalizedTangent parameter) := by
    unfold tangent source basePoint Conic.tangentLine parabola point
      normalizedTangent Line.Equivalent
    exact ⟨by ring1, by ring1, by ring1⟩
  exact ⟨onParabola, tangentEquivalent,
    Conic.tangentLine_contains source basePoint onParabola nonSingular⟩

/-- Away from characteristic two, every point—not merely a parametrized
one—lying on the displayed parabola is first-order non-singular. -/
theorem every_point_nonSingular [Nontrivial K]
    (fourNonzero : (4 : K) ≠ 0) (candidate : Point K)
    (_onParabola : (parabola (K := K)).Contains candidate) :
    (parabola (K := K)).IsNonSingularAt candidate := by
  unfold Conic.IsNonSingularAt parabola
  left
  intro gradientZero
  apply negative_four_nonzero fourNonzero
  calc
    (-4 : K) = -4 + 2 * 0 * candidate.x + 0 * candidate.y := by ring1
    _ = 0 := gradientZero

end ExampleNineteenFour

namespace ExerciseNineteenOne

/-- Focus `[a,0]` for the parabola `y²=4ax`. -/
def focus (parameter : K) : Point K := ⟨parameter, 0⟩

/-- Directrix `x=-a`, displayed as `⟨1:0:a⟩`. -/
def directrix [Nontrivial K] (parameter : K) : Line K where
  a := 1
  b := 0
  c := parameter
  direction_nonzero := Or.inl one_ne_zero

/-- The focus/directrix construction of `y²=4ax`. -/
def parabola [Nontrivial K] [DecidableEq K] (parameter : K) : Conic K :=
  Conic.parabolaConic (focus parameter) (directrix parameter)

theorem directrix_nonNull [Nontrivial K] (parameter : K) :
    ¬ (directrix parameter).IsNull := by
  intro nullLine
  unfold directrix Line.IsNull at nullLine
  have oneEqualsZero : (1 : K) = 0 := by
    calc
      (1 : K) = 1 ^ 2 + 0 ^ 2 := by ring1
      _ = 0 := nullLine
  exact (one_ne_zero : (1 : K) ≠ 0) oneEqualsZero

theorem focus_not_on_directrix [Nontrivial K]
    (parameter : K) (twoNonzero : (2 : K) ≠ 0)
    (parameterNonzero : parameter ≠ 0) :
    ¬ (directrix parameter).Contains (focus parameter) := by
  intro incidence
  have twiceParameterZero : 2 * parameter = 0 := by
    unfold directrix focus Line.Contains at incidence
    calc
      2 * parameter = 1 * parameter + 0 * 0 + parameter := by ring1
      _ = 0 := incidence
  exact (RFAP.ExplicitField.mul_ne_zero twoNonzero parameterNonzero)
    twiceParameterZero

/-- The displayed focus/directrix data provides the constructive parabola
certificate needed by Theorem 121. -/
theorem presentation [Nontrivial K] [DecidableEq K]
    (parameter : K) (twoNonzero : (2 : K) ≠ 0)
    (parameterNonzero : parameter ≠ 0) :
    (parabola parameter).IsParabolaPresentation
      (focus parameter) (directrix parameter) :=
  Conic.parabolaConic_isParabolaPresentation (focus parameter)
    (directrix parameter) (directrix_nonNull parameter)
    (focus_not_on_directrix parameter twoNonzero parameterNonzero)

/-- The focus/directrix construction expands to `y²-4ax=0`. -/
theorem parabola_coefficients [Nontrivial K] [DecidableEq K]
    (parameter : K) :
    let source := parabola parameter
    source.d = 0 ∧ source.e = 0 ∧ source.f = 1 ∧
      source.a = -4 * parameter ∧ source.b = 0 ∧ source.c = 0 := by
  dsimp only [parabola, Conic.parabolaConic, focus, directrix, lineNorm]
  exact ⟨by ring1, by ring1, by ring1, by ring1, by ring1, by ring1⟩

/-- Exercise 19.1: the direct focus/directrix specialization of the parabola
reflection theorem for `y²=4ax`. -/
theorem exercise_19_1 [Nontrivial K] [DecidableEq K]
    (parameter : K) (twoNonzero : (2 : K) ≠ 0)
    (parameterNonzero : parameter ≠ 0) (basePoint : Point K)
    (onParabola : (parabola parameter).Contains basePoint)
    (focusLineNonNull :
      ¬ (lineThrough basePoint (focus parameter)
        (Conic.parabola_point_ne_focus (parabola parameter)
          (focus parameter) basePoint (directrix parameter)
          (presentation parameter twoNonzero parameterNonzero)
          onParabola)).IsNull) :
    let parabolaPresentation :=
      presentation parameter twoNonzero parameterNonzero
    let pointFocusDistinct :=
      Conic.parabola_point_ne_focus (parabola parameter)
        (focus parameter) basePoint (directrix parameter)
        parabolaPresentation onParabola
    let nonSingular :=
      Conic.parabola_nonSingularAt (parabola parameter)
        (focus parameter) basePoint (directrix parameter) twoNonzero
        parabolaPresentation
    let tangent :=
      Conic.tangentLine (parabola parameter) basePoint nonSingular
    let focusLine := lineThrough basePoint (focus parameter) pointFocusDistinct
    let normalLine := altitudeThrough basePoint (directrix parameter)
    ∃ tangentNonNull : ¬ tangent.IsNull,
      ∃ normalLineNonNull : ¬ normalLine.IsNull,
        spread tangent focusLine tangentNonNull focusLineNonNull =
          spread tangent normalLine tangentNonNull normalLineNonNull := by
  exact Conic.parabola_reflection (parabola parameter) (focus parameter)
    basePoint (directrix parameter) twoNonzero
    (presentation parameter twoNonzero parameterNonzero) onParabola
    focusLineNonNull

end ExerciseNineteenOne

namespace ExerciseNineteenTwo

/-- The focus `[1,0]` of `y²=4x`. -/
def focus : Point K := ⟨1, 0⟩

/-- The parameter point `[t²,2t]`. -/
def point (parameter : K) : Point K :=
  ⟨parameter ^ 2, 2 * parameter⟩

/-- The tangent `⟨1:-t:t²⟩` at the parameter point. -/
def tangent [Nontrivial K] (parameter : K) : Line K where
  a := 1
  b := -parameter
  c := parameter ^ 2
  direction_nonzero := Or.inl one_ne_zero

/-- The explicit intersection `[t₁t₂,t₁+t₂]` of two parameter tangents. -/
def tangentIntersection (firstParameter secondParameter : K) : Point K :=
  ⟨firstParameter * secondParameter, firstParameter + secondParameter⟩

/-- Each normalized tangent contains its parameter point. -/
theorem tangent_contains_point [Nontrivial K] (parameter : K) :
    (tangent parameter).Contains (point parameter) := by
  unfold tangent point Line.Contains
  ring1

/-- The explicit intersection lies on both displayed tangents. -/
theorem tangent_intersection
    [Nontrivial K]
    (firstParameter secondParameter : K) :
    (tangent firstParameter).Contains
        (tangentIntersection firstParameter secondParameter) ∧
      (tangent secondParameter).Contains
        (tangentIntersection firstParameter secondParameter) := by
  unfold tangent tangentIntersection Line.Contains
  constructor <;> ring1

/-- Distinct parameters give genuinely distinct line proportions. -/
theorem tangents_not_equivalent
    [Nontrivial K]
    (firstParameter secondParameter : K)
    (parametersDistinct : firstParameter ≠ secondParameter) :
    ¬ (tangent firstParameter).Equivalent (tangent secondParameter) := by
  intro equivalent
  apply parametersDistinct
  have firstEquation := equivalent.1
  unfold tangent at firstEquation
  change (1 : K) * (-secondParameter) = 1 * (-firstParameter) at firstEquation
  have negativesEqual : -firstParameter = -secondParameter := by
    simpa only [one_mul] using firstEquation.symm
  calc
    firstParameter = -(-firstParameter) := by ring1
    _ = -(-secondParameter) := by rw [negativesEqual]
    _ = secondParameter := by ring1

/-- Exercise 19.2's quotient-free ratio statement.  The squares on the two
`Q(Aᵢ,B)` terms are essential and agree with the printed formula. -/
theorem exercise_19_2
    (firstParameter secondParameter : K) :
    quadrance (point firstParameter)
          (tangentIntersection firstParameter secondParameter) ^ 2 *
        quadrance (point secondParameter) focus =
      quadrance (point secondParameter)
          (tangentIntersection firstParameter secondParameter) ^ 2 *
        quadrance (point firstParameter) focus := by
  unfold point tangentIntersection focus quadrance
  ring1

namespace FieldElevenCheck

abbrev F₁₁ := FieldEleven.Element

/-- The book's exact `F₁₁` data: `A₁=[1,2]`, `A₂=[4,-4]`,
`B=[-2,-1]`, and both ratios normalize to `5`. -/
theorem field_eleven_example :
    point (K := F₁₁) 1 = ⟨1, 2⟩ ∧
      point (K := F₁₁) 9 = ⟨4, 7⟩ ∧
      tangentIntersection (K := F₁₁) 1 9 = ⟨9, 10⟩ ∧
      quadrance (point (K := F₁₁) 1)
          (tangentIntersection (K := F₁₁) 1 9) = 7 ∧
      quadrance (point (K := F₁₁) 9)
          (tangentIntersection (K := F₁₁) 1 9) = 1 ∧
      quadrance (point (K := F₁₁) 1) (focus (K := F₁₁)) = 4 ∧
      quadrance (point (K := F₁₁) 9) (focus (K := F₁₁)) = 3 ∧
      quadrance (point (K := F₁₁) 1)
          (tangentIntersection (K := F₁₁) 1 9) ^ 2 /
          quadrance (point (K := F₁₁) 9)
            (tangentIntersection (K := F₁₁) 1 9) ^ 2 = 5 ∧
      quadrance (point (K := F₁₁) 1) (focus (K := F₁₁)) /
          quadrance (point (K := F₁₁) 9) (focus (K := F₁₁)) = 5 := by
  unfold point tangentIntersection focus quadrance
  decide

end FieldElevenCheck

end ExerciseNineteenTwo

end ChapterNineteenExamples

end DivineProportions
