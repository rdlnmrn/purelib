import DivineProportions.Conics.Axis
import DivineProportions.Trigonometry.QuadranceToLine

/-!
# Divine Proportions, §15.5: grammolas

A grammola is retained through its two explicit non-null diagonal lines and
associated quadrance.  Multiplying by the two line norms clears exactly the
two finite divisions and produces an executable conic.  The intersection of
the diagonals is then an explicit center.
-/

namespace DivineProportions

namespace Grammola

variable {K : Type*} [RFAP.ExplicitField K]

/-- The nondegeneracy data in the definition of a grammola. -/
structure Presentation (firstDiagonal secondDiagonal : Line K)
    (associatedQuadrance : K) : Prop where
  firstNonNull : ¬ firstDiagonal.IsNull
  secondNonNull : ¬ secondDiagonal.IsNull
  notParallel : ¬ firstDiagonal.Parallel secondDiagonal
  notPerpendicular : ¬ firstDiagonal.Perpendicular secondDiagonal
  associatedNonzero : associatedQuadrance ≠ 0

/-- The metrical grammola equation before its two denominators are cleared. -/
def Contains (firstDiagonal secondDiagonal : Line K)
    (firstNonNull : ¬ firstDiagonal.IsNull)
    (secondNonNull : ¬ secondDiagonal.IsNull)
    (associatedQuadrance : K) (point : Point K) : Prop :=
  pointLineQuadrance point firstDiagonal firstNonNull +
      pointLineQuadrance point secondDiagonal secondNonNull =
    associatedQuadrance

/-- The linear expression represented by a displayed line at a point. -/
def lineValue (line : Line K) (point : Point K) : K :=
  line.a * point.x + line.b * point.y + line.c

/-- The denominator-cleared grammola polynomial. -/
def clearedEvaluate (firstDiagonal secondDiagonal : Line K)
    (associatedQuadrance : K) (point : Point K) : K :=
  lineNorm secondDiagonal * lineValue firstDiagonal point ^ 2 +
    lineNorm firstDiagonal * lineValue secondDiagonal point ^ 2 -
    associatedQuadrance * lineNorm firstDiagonal * lineNorm secondDiagonal

def conicD (firstDiagonal secondDiagonal : Line K) : K :=
  lineNorm secondDiagonal * firstDiagonal.a ^ 2 +
    lineNorm firstDiagonal * secondDiagonal.a ^ 2

def conicE (firstDiagonal secondDiagonal : Line K) : K :=
  2 * (lineNorm secondDiagonal * firstDiagonal.a * firstDiagonal.b +
    lineNorm firstDiagonal * secondDiagonal.a * secondDiagonal.b)

def conicF (firstDiagonal secondDiagonal : Line K) : K :=
  lineNorm secondDiagonal * firstDiagonal.b ^ 2 +
    lineNorm firstDiagonal * secondDiagonal.b ^ 2

def conicA (firstDiagonal secondDiagonal : Line K) : K :=
  2 * (lineNorm secondDiagonal * firstDiagonal.a * firstDiagonal.c +
    lineNorm firstDiagonal * secondDiagonal.a * secondDiagonal.c)

def conicB (firstDiagonal secondDiagonal : Line K) : K :=
  2 * (lineNorm secondDiagonal * firstDiagonal.b * firstDiagonal.c +
    lineNorm firstDiagonal * secondDiagonal.b * secondDiagonal.c)

def conicC (firstDiagonal secondDiagonal : Line K)
    (associatedQuadrance : K) : K :=
  lineNorm secondDiagonal * firstDiagonal.c ^ 2 +
    lineNorm firstDiagonal * secondDiagonal.c ^ 2 -
    associatedQuadrance * lineNorm firstDiagonal * lineNorm secondDiagonal

private theorem conic_quadratic_nonzero [DecidableEq K]
    (firstDiagonal secondDiagonal : Line K)
    (firstNonNull : ¬ firstDiagonal.IsNull)
    (secondNonNull : ¬ secondDiagonal.IsNull)
    (twoNonzero : (2 : K) ≠ 0) :
    conicD firstDiagonal secondDiagonal ≠ 0 ∨
      conicE firstDiagonal secondDiagonal ≠ 0 ∨
      conicF firstDiagonal secondDiagonal ≠ 0 := by
  by_cases dNonzero : conicD firstDiagonal secondDiagonal ≠ 0
  · exact Or.inl dNonzero
  · right
    right
    intro fZero
    have dZero : conicD firstDiagonal secondDiagonal = 0 := by
      by_cases dZero : conicD firstDiagonal secondDiagonal = 0
      · exact dZero
      · exact False.elim (dNonzero dZero)
    have normProductNonzero :
        lineNorm firstDiagonal * lineNorm secondDiagonal ≠ 0 :=
      RFAP.ExplicitField.mul_ne_zero firstNonNull secondNonNull
    have twiceProductNonzero :
        (2 : K) *
            (lineNorm firstDiagonal * lineNorm secondDiagonal) ≠ 0 :=
      RFAP.ExplicitField.mul_ne_zero twoNonzero normProductNonzero
    apply twiceProductNonzero
    calc
      (2 : K) * (lineNorm firstDiagonal * lineNorm secondDiagonal) =
          conicD firstDiagonal secondDiagonal +
            conicF firstDiagonal secondDiagonal := by
        unfold conicD conicF lineNorm
        ring1
      _ = 0 := by rw [dZero, fZero]; ring1

/-- The explicit six-coefficient conic obtained by clearing the two line
norms in the grammola equation. -/
def conic [DecidableEq K]
    (firstDiagonal secondDiagonal : Line K)
    (firstNonNull : ¬ firstDiagonal.IsNull)
    (secondNonNull : ¬ secondDiagonal.IsNull)
    (associatedQuadrance : K) (twoNonzero : (2 : K) ≠ 0) : Conic K where
  d := conicD firstDiagonal secondDiagonal
  e := conicE firstDiagonal secondDiagonal
  f := conicF firstDiagonal secondDiagonal
  a := conicA firstDiagonal secondDiagonal
  b := conicB firstDiagonal secondDiagonal
  c := conicC firstDiagonal secondDiagonal associatedQuadrance
  quadratic_nonzero := conic_quadratic_nonzero firstDiagonal secondDiagonal
    firstNonNull secondNonNull twoNonzero

/-- The sum of the two square coefficients is twice the product of the two
line norms.  In particular, it cannot vanish for a valid grammola outside
characteristic two. -/
theorem conic_trace [DecidableEq K]
    (firstDiagonal secondDiagonal : Line K)
    (firstNonNull : ¬ firstDiagonal.IsNull)
    (secondNonNull : ¬ secondDiagonal.IsNull)
    (associatedQuadrance : K) (twoNonzero : (2 : K) ≠ 0) :
    (conic firstDiagonal secondDiagonal firstNonNull secondNonNull
        associatedQuadrance twoNonzero).d +
      (conic firstDiagonal secondDiagonal firstNonNull secondNonNull
        associatedQuadrance twoNonzero).f =
      2 * lineNorm firstDiagonal * lineNorm secondDiagonal := by
  unfold conic conicD conicF lineNorm
  ring1

theorem conic_trace_nonzero [DecidableEq K]
    (firstDiagonal secondDiagonal : Line K)
    (firstNonNull : ¬ firstDiagonal.IsNull)
    (secondNonNull : ¬ secondDiagonal.IsNull)
    (associatedQuadrance : K) (twoNonzero : (2 : K) ≠ 0) :
    (conic firstDiagonal secondDiagonal firstNonNull secondNonNull
        associatedQuadrance twoNonzero).d +
      (conic firstDiagonal secondDiagonal firstNonNull secondNonNull
        associatedQuadrance twoNonzero).f ≠ 0 := by
  rw [conic_trace]
  exact RFAP.ExplicitField.mul_ne_zero
    (RFAP.ExplicitField.mul_ne_zero twoNonzero firstNonNull) secondNonNull

/-- Expansion of the explicit grammola conic is exactly the cleared metric
polynomial. -/
theorem conic_evaluate [DecidableEq K]
    (firstDiagonal secondDiagonal : Line K)
    (firstNonNull : ¬ firstDiagonal.IsNull)
    (secondNonNull : ¬ secondDiagonal.IsNull)
    (associatedQuadrance : K) (twoNonzero : (2 : K) ≠ 0)
    (point : Point K) :
    (conic firstDiagonal secondDiagonal firstNonNull secondNonNull
      associatedQuadrance twoNonzero).evaluate point =
        clearedEvaluate firstDiagonal secondDiagonal associatedQuadrance
          point := by
  unfold conic Conic.evaluate clearedEvaluate lineValue conicD conicE conicF
    conicA conicB conicC
  ring1

private theorem eq_zero_of_nonzero_mul_left
    {factor value : K} (factorNonzero : factor ≠ 0)
    (productZero : factor * value = 0) : value = 0 := by
  have cancel : factor⁻¹ * factor = (1 : K) := by
    calc
      factor⁻¹ * factor = factor * factor⁻¹ := by ring1
      _ = 1 := RFAP.ExplicitField.mul_inv_cancel factor factorNonzero
  calc
    value = 1 * value := by ring1
    _ = (factor⁻¹ * factor) * value := by rw [cancel]
    _ = factor⁻¹ * (factor * value) := by ring1
    _ = 0 := by rw [productZero]; ring1

/-- The cleared conic has exactly the original metrical grammola locus. -/
theorem conic_contains_iff [DecidableEq K]
    (firstDiagonal secondDiagonal : Line K)
    (firstNonNull : ¬ firstDiagonal.IsNull)
    (secondNonNull : ¬ secondDiagonal.IsNull)
    (associatedQuadrance : K) (twoNonzero : (2 : K) ≠ 0)
    (point : Point K) :
    (conic firstDiagonal secondDiagonal firstNonNull secondNonNull
        associatedQuadrance twoNonzero).Contains point ↔
      Contains firstDiagonal secondDiagonal firstNonNull secondNonNull
        associatedQuadrance point := by
  have firstCancel :
      lineNorm firstDiagonal * (lineNorm firstDiagonal)⁻¹ = (1 : K) :=
    RFAP.ExplicitField.mul_inv_cancel _ firstNonNull
  have secondCancel :
      lineNorm secondDiagonal * (lineNorm secondDiagonal)⁻¹ = (1 : K) :=
    RFAP.ExplicitField.mul_inv_cancel _ secondNonNull
  have normProductNonzero :
      lineNorm firstDiagonal * lineNorm secondDiagonal ≠ 0 :=
    RFAP.ExplicitField.mul_ne_zero firstNonNull secondNonNull
  have clearedFactor : ∀ source : Point K,
      clearedEvaluate firstDiagonal secondDiagonal associatedQuadrance source =
        (lineNorm firstDiagonal * lineNorm secondDiagonal) *
          (pointLineQuadrance source firstDiagonal firstNonNull +
            pointLineQuadrance source secondDiagonal secondNonNull -
            associatedQuadrance) := by
    intro source
    rw [pointLineQuadrance_formula, pointLineQuadrance_formula]
    simp only [RFAP.ExplicitField.div_eq_mul_inv]
    unfold clearedEvaluate lineValue
    calc
      lineNorm secondDiagonal *
              (firstDiagonal.a * source.x + firstDiagonal.b * source.y +
                firstDiagonal.c) ^ 2 +
            lineNorm firstDiagonal *
              (secondDiagonal.a * source.x + secondDiagonal.b * source.y +
                secondDiagonal.c) ^ 2 -
            associatedQuadrance * lineNorm firstDiagonal *
              lineNorm secondDiagonal =
          lineNorm secondDiagonal *
              (firstDiagonal.a * source.x + firstDiagonal.b * source.y +
                firstDiagonal.c) ^ 2 *
                (lineNorm firstDiagonal * (lineNorm firstDiagonal)⁻¹) +
            lineNorm firstDiagonal *
              (secondDiagonal.a * source.x + secondDiagonal.b * source.y +
                secondDiagonal.c) ^ 2 *
                (lineNorm secondDiagonal * (lineNorm secondDiagonal)⁻¹) -
            associatedQuadrance * lineNorm firstDiagonal *
              lineNorm secondDiagonal := by
        rw [firstCancel, secondCancel]
        ring1
      _ = lineNorm firstDiagonal * lineNorm secondDiagonal *
          ((firstDiagonal.a * source.x + firstDiagonal.b * source.y +
                firstDiagonal.c) ^ 2 * (lineNorm firstDiagonal)⁻¹ +
            (secondDiagonal.a * source.x + secondDiagonal.b * source.y +
                secondDiagonal.c) ^ 2 * (lineNorm secondDiagonal)⁻¹ -
            associatedQuadrance) := by ring1
  constructor
  · intro onConic
    unfold Conic.Contains at onConic
    rw [conic_evaluate, clearedFactor] at onConic
    have differenceZero :=
      eq_zero_of_nonzero_mul_left normProductNonzero onConic
    unfold Contains
    calc
      pointLineQuadrance point firstDiagonal firstNonNull +
          pointLineQuadrance point secondDiagonal secondNonNull =
        (pointLineQuadrance point firstDiagonal firstNonNull +
            pointLineQuadrance point secondDiagonal secondNonNull -
            associatedQuadrance) + associatedQuadrance := by ring1
      _ = associatedQuadrance := by rw [differenceZero]; ring1
  · intro metricEquation
    unfold Conic.Contains
    rw [conic_evaluate, clearedFactor]
    unfold Contains at metricEquation
    have differenceZero :
        pointLineQuadrance point firstDiagonal firstNonNull +
            pointLineQuadrance point secondDiagonal secondNonNull -
            associatedQuadrance = 0 := by
      rw [metricEquation]
      ring1
    rw [differenceZero]
    ring1

/-- Exercise 15.15: every grammola is centered at the explicit intersection
of its two nonparallel diagonal lines. -/
theorem exercise_15_15 [DecidableEq K]
    (firstDiagonal secondDiagonal : Line K) (associatedQuadrance : K)
    (presentation :
      Presentation firstDiagonal secondDiagonal associatedQuadrance)
    (twoNonzero : (2 : K) ≠ 0) :
    (conic firstDiagonal secondDiagonal presentation.firstNonNull
      presentation.secondNonNull associatedQuadrance twoNonzero).IsCenter
        (lineIntersection firstDiagonal secondDiagonal
          presentation.notParallel) := by
  let center :=
    lineIntersection firstDiagonal secondDiagonal presentation.notParallel
  have onFirst : firstDiagonal.Contains center :=
    lineIntersection_on_first firstDiagonal secondDiagonal
      presentation.notParallel
  have onSecond : secondDiagonal.Contains center :=
    lineIntersection_on_second firstDiagonal secondDiagonal
      presentation.notParallel
  unfold Line.Contains at onFirst onSecond
  constructor
  · change
      2 * conicD firstDiagonal secondDiagonal * center.x +
          conicE firstDiagonal secondDiagonal * center.y +
          conicA firstDiagonal secondDiagonal = 0
    calc
      2 * conicD firstDiagonal secondDiagonal * center.x +
            conicE firstDiagonal secondDiagonal * center.y +
            conicA firstDiagonal secondDiagonal =
          2 * (lineNorm secondDiagonal * firstDiagonal.a *
              (firstDiagonal.a * center.x + firstDiagonal.b * center.y +
                firstDiagonal.c) +
            lineNorm firstDiagonal * secondDiagonal.a *
              (secondDiagonal.a * center.x + secondDiagonal.b * center.y +
                secondDiagonal.c)) := by
        unfold conicD conicE conicA
        ring1
      _ = 0 := by rw [onFirst, onSecond]; ring1
  · change
      conicE firstDiagonal secondDiagonal * center.x +
          2 * conicF firstDiagonal secondDiagonal * center.y +
          conicB firstDiagonal secondDiagonal = 0
    calc
      conicE firstDiagonal secondDiagonal * center.x +
            2 * conicF firstDiagonal secondDiagonal * center.y +
            conicB firstDiagonal secondDiagonal =
          2 * (lineNorm secondDiagonal * firstDiagonal.b *
              (firstDiagonal.a * center.x + firstDiagonal.b * center.y +
                firstDiagonal.c) +
            lineNorm firstDiagonal * secondDiagonal.b *
              (secondDiagonal.a * center.x + secondDiagonal.b * center.y +
                secondDiagonal.c)) := by
        unfold conicE conicF conicB
        ring1
      _ = 0 := by rw [onFirst, onSecond]; ring1

/-- The first diagonal `⟨a:-1:0⟩` in Example 15.7. -/
def example15SevenFirstDiagonal [Nontrivial K] (a : K) : Line K where
  a := a
  b := -1
  c := 0
  direction_nonzero := Or.inr (by
    intro negativeOneZero
    apply (one_ne_zero : (1 : K) ≠ 0)
    calc
      (1 : K) = -(-1) := by ring1
      _ = 0 := by rw [negativeOneZero]; ring1)

/-- The second diagonal `⟨a:1:0⟩` in Example 15.7. -/
def example15SevenSecondDiagonal [Nontrivial K] (a : K) : Line K where
  a := a
  b := 1
  c := 0
  direction_nonzero := Or.inr (one_ne_zero : (1 : K) ≠ 0)

theorem example15SevenFirst_nonNull [Nontrivial K] (a : K)
    (normNonzero : a ^ 2 + 1 ≠ 0) :
    ¬ (example15SevenFirstDiagonal a).IsNull := by
  intro null
  apply normNonzero
  calc
    a ^ 2 + 1 =
        (example15SevenFirstDiagonal a).a ^ 2 +
          (example15SevenFirstDiagonal a).b ^ 2 := by
      unfold example15SevenFirstDiagonal
      ring1
    _ = 0 := null

theorem example15SevenSecond_nonNull [Nontrivial K] (a : K)
    (normNonzero : a ^ 2 + 1 ≠ 0) :
    ¬ (example15SevenSecondDiagonal a).IsNull := by
  intro null
  apply normNonzero
  calc
    a ^ 2 + 1 =
        (example15SevenSecondDiagonal a).a ^ 2 +
          (example15SevenSecondDiagonal a).b ^ 2 := by
      unfold example15SevenSecondDiagonal
      ring1
    _ = 0 := null

/-- Example 15.7's diagonal data form a grammola presentation.  Besides the
printed `a ≠ ±1`, the definition also requires `a ≠ 0` (otherwise the
two displayed lines coincide) and `a²+1 ≠ 0` (otherwise they are null).
These necessary source hypotheses are explicit here. -/
theorem example_15_7_presentation [Nontrivial K]
    (a associatedQuadrance : K) (aNonzero : a ≠ 0)
    (normNonzero : a ^ 2 + 1 ≠ 0) (notSquareOne : a ^ 2 ≠ 1)
    (associatedNonzero : associatedQuadrance ≠ 0)
    (twoNonzero : (2 : K) ≠ 0) :
    Presentation (example15SevenFirstDiagonal a)
      (example15SevenSecondDiagonal a) associatedQuadrance := by
  have firstNonNull := example15SevenFirst_nonNull a normNonzero
  have secondNonNull := example15SevenSecond_nonNull a normNonzero
  refine ⟨firstNonNull, secondNonNull, ?_, ?_, associatedNonzero⟩
  · intro parallel
    have twiceANonzero : (2 : K) * a ≠ 0 :=
      RFAP.ExplicitField.mul_ne_zero twoNonzero aNonzero
    apply twiceANonzero
    calc
      (2 : K) * a =
          (example15SevenFirstDiagonal a).a *
              (example15SevenSecondDiagonal a).b -
            (example15SevenSecondDiagonal a).a *
              (example15SevenFirstDiagonal a).b := by
        unfold example15SevenFirstDiagonal example15SevenSecondDiagonal
        ring1
      _ = 0 := parallel
  · intro perpendicular
    apply notSquareOne
    calc
      a ^ 2 =
          ((example15SevenFirstDiagonal a).a *
              (example15SevenSecondDiagonal a).a +
            (example15SevenFirstDiagonal a).b *
              (example15SevenSecondDiagonal a).b) + 1 := by
        unfold example15SevenFirstDiagonal example15SevenSecondDiagonal
        ring1
      _ = 1 := by rw [perpendicular]; ring1

/-- Example 15.7: clearing the common nonzero line norm gives exactly
`2a²x²+2y²=K(a²+1)`. -/
theorem example_15_7_equation [Nontrivial K] [DecidableEq K]
    (a associatedQuadrance : K) (normNonzero : a ^ 2 + 1 ≠ 0)
    (point : Point K) :
    Contains (example15SevenFirstDiagonal a)
        (example15SevenSecondDiagonal a)
        (example15SevenFirst_nonNull a normNonzero)
        (example15SevenSecond_nonNull a normNonzero)
        associatedQuadrance point ↔
      2 * a ^ 2 * point.x ^ 2 + 2 * point.y ^ 2 =
        associatedQuadrance * (a ^ 2 + 1) := by
  have normCancel : (a ^ 2 + 1) * (a ^ 2 + 1)⁻¹ = (1 : K) :=
    RFAP.ExplicitField.mul_inv_cancel _ normNonzero
  unfold Contains
  rw [pointLineQuadrance_formula, pointLineQuadrance_formula]
  unfold example15SevenFirstDiagonal example15SevenSecondDiagonal lineNorm
  have firstValue : a * point.x + -1 * point.y + 0 =
      a * point.x - point.y := by ring1
  have secondValue : a * point.x + 1 * point.y + 0 =
      a * point.x + point.y := by ring1
  have firstNorm : a ^ 2 + (-1 : K) ^ 2 = a ^ 2 + 1 := by ring1
  have secondNorm : a ^ 2 + (1 : K) ^ 2 = a ^ 2 + 1 := by ring1
  rw [firstValue, secondValue, firstNorm, secondNorm]
  simp only [RFAP.ExplicitField.div_eq_mul_inv]
  constructor
  · intro metricEquation
    calc
      2 * a ^ 2 * point.x ^ 2 + 2 * point.y ^ 2 =
          (a * point.x - point.y) ^ 2 +
            (a * point.x + point.y) ^ 2 := by ring1
      _ = ((a * point.x - point.y) ^ 2 +
            (a * point.x + point.y) ^ 2) *
          ((a ^ 2 + 1) * (a ^ 2 + 1)⁻¹) := by
        rw [normCancel]
        ring1
      _ = (a ^ 2 + 1) *
          ((a * point.x - point.y) ^ 2 * (a ^ 2 + 1)⁻¹ +
            (a * point.x + point.y) ^ 2 * (a ^ 2 + 1)⁻¹) := by
        ring1
      _ = (a ^ 2 + 1) * associatedQuadrance := by
        rw [metricEquation]
      _ = associatedQuadrance * (a ^ 2 + 1) := by ring1
  · intro clearedEquation
    have productZero :
        (a ^ 2 + 1) *
          ((a * point.x - point.y) ^ 2 * (a ^ 2 + 1)⁻¹ +
            (a * point.x + point.y) ^ 2 * (a ^ 2 + 1)⁻¹ -
            associatedQuadrance) = 0 := by
      calc
        (a ^ 2 + 1) *
              ((a * point.x - point.y) ^ 2 * (a ^ 2 + 1)⁻¹ +
                (a * point.x + point.y) ^ 2 * (a ^ 2 + 1)⁻¹ -
                associatedQuadrance) =
            2 * a ^ 2 * point.x ^ 2 + 2 * point.y ^ 2 -
              associatedQuadrance * (a ^ 2 + 1) := by
          calc
            (a ^ 2 + 1) *
                  ((a * point.x - point.y) ^ 2 * (a ^ 2 + 1)⁻¹ +
                    (a * point.x + point.y) ^ 2 * (a ^ 2 + 1)⁻¹ -
                    associatedQuadrance) =
                ((a * point.x - point.y) ^ 2 +
                  (a * point.x + point.y) ^ 2) *
                    ((a ^ 2 + 1) * (a ^ 2 + 1)⁻¹) -
                  associatedQuadrance * (a ^ 2 + 1) := by ring1
            _ = 2 * a ^ 2 * point.x ^ 2 + 2 * point.y ^ 2 -
                associatedQuadrance * (a ^ 2 + 1) := by
              rw [normCancel]
              ring1
        _ = 0 := by rw [clearedEquation]; ring1
    have differenceZero :=
      eq_zero_of_nonzero_mul_left normNonzero productZero
    calc
      (a * point.x - point.y) ^ 2 * (a ^ 2 + 1)⁻¹ +
          (a * point.x + point.y) ^ 2 * (a ^ 2 + 1)⁻¹ =
        ((a * point.x - point.y) ^ 2 * (a ^ 2 + 1)⁻¹ +
          (a * point.x + point.y) ^ 2 * (a ^ 2 + 1)⁻¹ -
          associatedQuadrance) + associatedQuadrance := by ring1
      _ = associatedQuadrance := by rw [differenceZero]; ring1

end Grammola

end DivineProportions
