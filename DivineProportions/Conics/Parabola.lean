import mathlib.Tactic.QuotientFreeRing
import DivineProportions.Conics.Circle
import DivineProportions.Trigonometry.QuadranceToLine

/-!
# Divine Proportions, §15.3: parabolas

The six coefficient equations below are the denominator-cleared expansion of
`Q(X,F) = Q(X,l)`.  An explicit nonzero scale retains the source's proportional
conic notation without a quotient or a selected representative.
-/

namespace DivineProportions

variable {K : Type*} [RFAP.ExplicitField K]

namespace Conic

/-- The denominator-cleared conic associated with a focus and directrix. -/
def parabolaConic [DecidableEq K] (focus : Point K)
    (directrix : Line K) : Conic K where
  d := directrix.b ^ 2
  e := -2 * directrix.a * directrix.b
  f := directrix.a ^ 2
  a := -2 * directrix.a * directrix.c -
    2 * lineNorm directrix * focus.x
  b := -2 * directrix.b * directrix.c -
    2 * lineNorm directrix * focus.y
  c := lineNorm directrix * (focus.x ^ 2 + focus.y ^ 2) -
    directrix.c ^ 2
  quadratic_nonzero := by
    by_cases aZero : directrix.a = 0
    · rcases directrix.direction_nonzero with aNonzero | bNonzero
      · exact False.elim (aNonzero aZero)
      · exact Or.inl (by
          simpa only [pow_two] using
            RFAP.ExplicitField.mul_ne_zero bNonzero bNonzero)
    · exact Or.inr (Or.inr
        (by
          simpa only [pow_two] using
            RFAP.ExplicitField.mul_ne_zero aZero aZero))

/-- Data for a scaled six-coefficient certificate that a conic is the parabola
with the displayed focus and directrix. -/
structure ParabolaPresentationData (conic : Conic K) (focus : Point K)
    (directrix : Line K) where
  directrixNonNull : ¬ directrix.IsNull
  focusNotOnDirectrix : ¬ directrix.Contains focus
  scale : K
  scaleNonzero : scale ≠ 0
  dEquation : conic.d = scale * directrix.b ^ 2
  eEquation : conic.e = scale * (-2 * directrix.a * directrix.b)
  fEquation : conic.f = scale * directrix.a ^ 2
  aEquation : conic.a = scale *
    (-2 * directrix.a * directrix.c -
      2 * lineNorm directrix * focus.x)
  bEquation : conic.b = scale *
    (-2 * directrix.b * directrix.c -
      2 * lineNorm directrix * focus.y)
  cEquation : conic.c = scale *
    (lineNorm directrix * (focus.x ^ 2 + focus.y ^ 2) -
      directrix.c ^ 2)

/-- The proposition asserting an explicitly witnessed scaled presentation. -/
def IsParabolaPresentation (conic : Conic K) (focus : Point K)
    (directrix : Line K) : Prop :=
  Nonempty (ParabolaPresentationData conic focus directrix)

/-- A parabola is a conic with an explicitly exhibited valid focus/directrix
presentation. -/
def IsParabola (conic : Conic K) : Prop :=
  ∃ focus : Point K, ∃ directrix : Line K,
    conic.IsParabolaPresentation focus directrix

/-- The unscaled construction has the evident presentation. -/
theorem parabolaConic_isParabolaPresentation [DecidableEq K] [Nontrivial K]
    (focus : Point K) (directrix : Line K)
    (directrixNonNull : ¬ directrix.IsNull)
    (focusNotOnDirectrix : ¬ directrix.Contains focus) :
    (parabolaConic focus directrix).IsParabolaPresentation
      focus directrix := by
  refine ⟨
    { directrixNonNull := directrixNonNull
      focusNotOnDirectrix := focusNotOnDirectrix
      scale := 1
      scaleNonzero := one_ne_zero
      dEquation := ?_
      eEquation := ?_
      fEquation := ?_
      aEquation := ?_
      bEquation := ?_
      cEquation := ?_ }⟩
  all_goals (unfold parabolaConic; ring1)

/-- Direct expansion of the denominator-cleared focus/directrix equation. -/
theorem parabolaConic_evaluate [DecidableEq K]
    (focus point : Point K) (directrix : Line K) :
    (parabolaConic focus directrix).evaluate point =
      lineNorm directrix * quadrance point focus -
        (directrix.a * point.x + directrix.b * point.y + directrix.c) ^ 2 := by
  unfold parabolaConic evaluate lineNorm quadrance
  ring1

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
    _ = factor⁻¹ * (factor * value) := mul_assoc _ _ _
    _ = 0 := by rw [productZero]; ring1

private theorem eq_of_mul_eq_mul_left
    {factor left right : K} (factorNonzero : factor ≠ 0)
    (productsEqual : factor * left = factor * right) : left = right := by
  have differenceZero : factor * (left - right) = 0 := by
    calc
      factor * (left - right) = factor * left - factor * right := by ring1
      _ = 0 := by rw [productsEqual]; ring1
  have cancelled := eq_zero_of_mul_eq_zero_left factorNonzero differenceZero
  calc
    left = (left - right) + right := by ring1
    _ = right := by rw [cancelled]; ring1

private theorem div_eq_of_eq_mul_right
    {numerator denominator value : K}
    (denominatorNonzero : denominator ≠ 0)
    (equation : numerator = denominator * value) :
    numerator / denominator = value := by
  have denominatorCancel :
      denominator * denominator⁻¹ = (1 : K) :=
    RFAP.ExplicitField.mul_inv_cancel denominator denominatorNonzero
  rw [RFAP.ExplicitField.div_eq_mul_inv, equation]
  calc
    denominator * value * denominator⁻¹ =
        value * (denominator * denominator⁻¹) := by ring1
    _ = value := by rw [denominatorCancel]; ring1

/-- Normalized data in the source's `directrix.a ≠ 0` chart. -/
private structure ParabolaAChart (conic : Conic K) (focus : Point K)
    (directrix : Line K) where
  beta : K
  gamma : K
  conicFNonzero : conic.f ≠ 0
  lineB : directrix.b = beta * directrix.a
  lineC : directrix.c = gamma * directrix.a
  normalizedNormNonzero : 1 + beta ^ 2 ≠ 0
  normalizedFocusOff : focus.x + beta * focus.y + gamma ≠ 0
  eNormalized : conic.e / conic.f = -2 * beta
  aNormalized : conic.a / conic.f =
    -2 * gamma - 2 * (1 + beta ^ 2) * focus.x
  bNormalized : conic.b / conic.f =
    -2 * beta * gamma - 2 * (1 + beta ^ 2) * focus.y
  cNormalized : conic.c / conic.f =
    (1 + beta ^ 2) * (focus.x ^ 2 + focus.y ^ 2) - gamma ^ 2

/-- Construct the normalized `a ≠ 0` chart by explicit division. -/
private def parabolaAChart (conic : Conic K) (focus : Point K)
    (directrix : Line K)
    (presentation : ParabolaPresentationData conic focus directrix)
    (directrixANonzero : directrix.a ≠ 0) :
    ParabolaAChart conic focus directrix := by
  let beta := directrix.b / directrix.a
  let gamma := directrix.c / directrix.a
  have lineB : directrix.b = beta * directrix.a := by
    calc
      directrix.b =
          (directrix.b / directrix.a) * directrix.a :=
        (RFAP.ExplicitField.div_mul_cancel directrix.b
          directrixANonzero).symm
      _ = beta * directrix.a := rfl
  have lineC : directrix.c = gamma * directrix.a := by
    calc
      directrix.c =
          (directrix.c / directrix.a) * directrix.a :=
        (RFAP.ExplicitField.div_mul_cancel directrix.c
          directrixANonzero).symm
      _ = gamma * directrix.a := rfl
  have aSquareNonzero : directrix.a ^ 2 ≠ 0 := by
    simpa only [pow_two] using
      RFAP.ExplicitField.mul_ne_zero directrixANonzero directrixANonzero
  have conicFNonzero : conic.f ≠ 0 := by
    rw [presentation.fEquation]
    exact RFAP.ExplicitField.mul_ne_zero presentation.scaleNonzero
      aSquareNonzero
  have normalizedNormNonzero : 1 + beta ^ 2 ≠ 0 := by
    intro normalizedNormZero
    apply presentation.directrixNonNull
    unfold Line.IsNull
    calc
      directrix.a ^ 2 + directrix.b ^ 2 =
          directrix.a ^ 2 * (1 + beta ^ 2) := by
        rw [lineB]
        ring1
      _ = 0 := by rw [normalizedNormZero]; ring1
  have normalizedFocusOff :
      focus.x + beta * focus.y + gamma ≠ 0 := by
    intro normalizedIncidence
    apply presentation.focusNotOnDirectrix
    unfold Line.Contains
    calc
      directrix.a * focus.x + directrix.b * focus.y + directrix.c =
          directrix.a * (focus.x + beta * focus.y + gamma) := by
        rw [lineB, lineC]
        ring1
      _ = 0 := by rw [normalizedIncidence]; ring1
  refine
    { beta := beta
      gamma := gamma
      conicFNonzero := conicFNonzero
      lineB := lineB
      lineC := lineC
      normalizedNormNonzero := normalizedNormNonzero
      normalizedFocusOff := normalizedFocusOff
      eNormalized := ?_
      aNormalized := ?_
      bNormalized := ?_
      cNormalized := ?_ }
  · apply div_eq_of_eq_mul_right conicFNonzero
    calc
      conic.e = presentation.scale *
          (-2 * directrix.a * directrix.b) := presentation.eEquation
      _ = conic.f * (-2 * beta) := by
        rw [presentation.fEquation, lineB]
        ring1
  · apply div_eq_of_eq_mul_right conicFNonzero
    calc
      conic.a = presentation.scale *
          (-2 * directrix.a * directrix.c -
            2 * lineNorm directrix * focus.x) := presentation.aEquation
      _ = conic.f *
          (-2 * gamma - 2 * (1 + beta ^ 2) * focus.x) := by
        rw [presentation.fEquation]
        unfold lineNorm
        rw [lineB, lineC]
        ring1
  · apply div_eq_of_eq_mul_right conicFNonzero
    calc
      conic.b = presentation.scale *
          (-2 * directrix.b * directrix.c -
            2 * lineNorm directrix * focus.y) := presentation.bEquation
      _ = conic.f *
          (-2 * beta * gamma -
            2 * (1 + beta ^ 2) * focus.y) := by
        rw [presentation.fEquation]
        unfold lineNorm
        rw [lineB, lineC]
        ring1
  · apply div_eq_of_eq_mul_right conicFNonzero
    calc
      conic.c = presentation.scale *
          (lineNorm directrix * (focus.x ^ 2 + focus.y ^ 2) -
            directrix.c ^ 2) := presentation.cEquation
      _ = conic.f *
          ((1 + beta ^ 2) * (focus.x ^ 2 + focus.y ^ 2) -
            gamma ^ 2) := by
        rw [presentation.fEquation]
        unfold lineNorm
        rw [lineB, lineC]
        ring1

private theorem negative_two_nonzero (twoNonzero : (2 : K) ≠ 0) :
    (-2 : K) ≠ 0 := by
  intro negativeTwoZero
  apply twoNonzero
  calc
    (2 : K) = -(-2) := by ring1
    _ = -0 := by rw [negativeTwoZero]
    _ = 0 := neg_zero

/-- Uniqueness of the source's recovered data in the `a ≠ 0` chart. -/
private theorem parabolaACharts_unique
    (conic : Conic K) (focus otherFocus : Point K)
    (directrix otherDirectrix : Line K) (twoNonzero : (2 : K) ≠ 0)
    (first : ParabolaAChart conic focus directrix)
    (second : ParabolaAChart conic otherFocus otherDirectrix) :
    focus = otherFocus ∧ first.beta = second.beta ∧
      first.gamma = second.gamma := by
  have betaEqual : first.beta = second.beta := by
    apply eq_of_mul_eq_mul_left (negative_two_nonzero twoNonzero)
    calc
      (-2 : K) * first.beta = conic.e / conic.f :=
        first.eNormalized.symm
      _ = (-2 : K) * second.beta := second.eNormalized
  have secondANormalized :
      conic.a / conic.f =
        -2 * second.gamma -
          2 * (1 + first.beta ^ 2) * otherFocus.x := by
    simpa only [← betaEqual] using second.aNormalized
  have secondBNormalized :
      conic.b / conic.f =
        -2 * first.beta * second.gamma -
          2 * (1 + first.beta ^ 2) * otherFocus.y := by
    simpa only [← betaEqual] using second.bNormalized
  have secondCNormalized :
      conic.c / conic.f =
        (1 + first.beta ^ 2) *
            (otherFocus.x ^ 2 + otherFocus.y ^ 2) -
          second.gamma ^ 2 := by
    simpa only [← betaEqual] using second.cNormalized
  have firstIdentity :
      (conic.a / conic.f) ^ 2 + (conic.b / conic.f) ^ 2 +
          4 * (conic.a / conic.f +
            (conic.b / conic.f) * first.beta) * first.gamma =
        4 * (1 + first.beta ^ 2) * (conic.c / conic.f) := by
    rw [first.aNormalized, first.bNormalized, first.cNormalized]
    ring1
  have secondIdentity :
      (conic.a / conic.f) ^ 2 + (conic.b / conic.f) ^ 2 +
          4 * (conic.a / conic.f +
            (conic.b / conic.f) * first.beta) * second.gamma =
        4 * (1 + first.beta ^ 2) * (conic.c / conic.f) := by
    rw [secondANormalized, secondBNormalized, secondCNormalized]
    ring1
  have linearFormula :
      conic.a / conic.f + (conic.b / conic.f) * first.beta =
        -2 * (1 + first.beta ^ 2) *
          (focus.x + first.beta * focus.y + first.gamma) := by
    rw [first.aNormalized, first.bNormalized]
    ring1
  have linearNonzero :
      conic.a / conic.f + (conic.b / conic.f) * first.beta ≠ 0 := by
    have productNonzero :
        (-2 : K) * (1 + first.beta ^ 2) *
            (focus.x + first.beta * focus.y + first.gamma) ≠ 0 :=
      RFAP.ExplicitField.mul_ne_zero
        (RFAP.ExplicitField.mul_ne_zero
          (negative_two_nonzero twoNonzero)
          first.normalizedNormNonzero)
        first.normalizedFocusOff
    intro linearZero
    apply productNonzero
    calc
      (-2 : K) * (1 + first.beta ^ 2) *
          (focus.x + first.beta * focus.y + first.gamma) =
        conic.a / conic.f + (conic.b / conic.f) * first.beta :=
          linearFormula.symm
      _ = 0 := linearZero
  have fourNonzero : (4 : K) ≠ 0 := by
    have twoTimesTwoNonzero : (2 : K) * 2 ≠ 0 :=
      RFAP.ExplicitField.mul_ne_zero twoNonzero twoNonzero
    intro fourZero
    apply twoTimesTwoNonzero
    calc
      (2 : K) * 2 = 4 := by ring1
      _ = 0 := fourZero
  have gammaFactorNonzero :
      4 * (conic.a / conic.f +
        (conic.b / conic.f) * first.beta) ≠ 0 :=
    RFAP.ExplicitField.mul_ne_zero fourNonzero linearNonzero
  have gammaProductsEqual :
      4 * (conic.a / conic.f +
          (conic.b / conic.f) * first.beta) * first.gamma =
        4 * (conic.a / conic.f +
          (conic.b / conic.f) * first.beta) * second.gamma := by
    calc
      4 * (conic.a / conic.f +
            (conic.b / conic.f) * first.beta) * first.gamma =
        ((conic.a / conic.f) ^ 2 + (conic.b / conic.f) ^ 2 +
            4 * (conic.a / conic.f +
              (conic.b / conic.f) * first.beta) * first.gamma) -
          ((conic.a / conic.f) ^ 2 + (conic.b / conic.f) ^ 2) := by
            ring1
      _ = 4 * (1 + first.beta ^ 2) * (conic.c / conic.f) -
          ((conic.a / conic.f) ^ 2 + (conic.b / conic.f) ^ 2) := by
        rw [firstIdentity]
      _ = ((conic.a / conic.f) ^ 2 + (conic.b / conic.f) ^ 2 +
            4 * (conic.a / conic.f +
              (conic.b / conic.f) * first.beta) * second.gamma) -
          ((conic.a / conic.f) ^ 2 + (conic.b / conic.f) ^ 2) := by
        rw [secondIdentity]
      _ = 4 * (conic.a / conic.f +
          (conic.b / conic.f) * first.beta) * second.gamma := by ring1
  have gammaEqual : first.gamma = second.gamma :=
    eq_of_mul_eq_mul_left gammaFactorNonzero gammaProductsEqual
  have coordinateFactorNonzero :
      2 * (1 + first.beta ^ 2) ≠ 0 :=
    RFAP.ExplicitField.mul_ne_zero twoNonzero
      first.normalizedNormNonzero
  have xProductsEqual :
      2 * (1 + first.beta ^ 2) * focus.x =
        2 * (1 + first.beta ^ 2) * otherFocus.x := by
    calc
      2 * (1 + first.beta ^ 2) * focus.x =
          -2 * first.gamma - conic.a / conic.f := by
        rw [first.aNormalized]
        ring1
      _ = -2 * second.gamma - conic.a / conic.f := by rw [gammaEqual]
      _ = 2 * (1 + first.beta ^ 2) * otherFocus.x := by
        rw [secondANormalized]
        ring1
  have yProductsEqual :
      2 * (1 + first.beta ^ 2) * focus.y =
        2 * (1 + first.beta ^ 2) * otherFocus.y := by
    calc
      2 * (1 + first.beta ^ 2) * focus.y =
          -2 * first.beta * first.gamma - conic.b / conic.f := by
        rw [first.bNormalized]
        ring1
      _ = -2 * first.beta * second.gamma - conic.b / conic.f := by
        rw [gammaEqual]
      _ = 2 * (1 + first.beta ^ 2) * otherFocus.y := by
        rw [secondBNormalized]
        ring1
  have xEqual :=
    eq_of_mul_eq_mul_left coordinateFactorNonzero xProductsEqual
  have yEqual :=
    eq_of_mul_eq_mul_left coordinateFactorNonzero yProductsEqual
  exact ⟨Point.ext xEqual yEqual, betaEqual, gammaEqual⟩

/-- Normalized data in the complementary `directrix.a = 0` chart. -/
private structure ParabolaBChart (conic : Conic K) (focus : Point K)
    (directrix : Line K) where
  delta : K
  lineAZero : directrix.a = 0
  conicDNonzero : conic.d ≠ 0
  lineC : directrix.c = delta * directrix.b
  normalizedFocusOff : focus.y + delta ≠ 0
  aNormalized : conic.a / conic.d = -2 * focus.x
  bNormalized : conic.b / conic.d = -2 * delta - 2 * focus.y
  cNormalized : conic.c / conic.d =
    focus.x ^ 2 + focus.y ^ 2 - delta ^ 2

/-- Construct the normalized horizontal-directrix chart by explicit division. -/
private def parabolaBChart (conic : Conic K) (focus : Point K)
    (directrix : Line K)
    (presentation : ParabolaPresentationData conic focus directrix)
    (directrixAZero : directrix.a = 0) :
    ParabolaBChart conic focus directrix := by
  have directrixBNonzero : directrix.b ≠ 0 := by
    rcases directrix.direction_nonzero with aNonzero | bNonzero
    · exact False.elim (aNonzero directrixAZero)
    · exact bNonzero
  let delta := directrix.c / directrix.b
  have lineC : directrix.c = delta * directrix.b := by
    calc
      directrix.c =
          (directrix.c / directrix.b) * directrix.b :=
        (RFAP.ExplicitField.div_mul_cancel directrix.c
          directrixBNonzero).symm
      _ = delta * directrix.b := rfl
  have bSquareNonzero : directrix.b ^ 2 ≠ 0 := by
    simpa only [pow_two] using
      RFAP.ExplicitField.mul_ne_zero directrixBNonzero directrixBNonzero
  have conicDNonzero : conic.d ≠ 0 := by
    rw [presentation.dEquation]
    exact RFAP.ExplicitField.mul_ne_zero presentation.scaleNonzero
      bSquareNonzero
  have normalizedFocusOff : focus.y + delta ≠ 0 := by
    intro normalizedIncidence
    apply presentation.focusNotOnDirectrix
    unfold Line.Contains
    calc
      directrix.a * focus.x + directrix.b * focus.y + directrix.c =
          directrix.b * (focus.y + delta) := by
        rw [directrixAZero, lineC]
        ring1
      _ = 0 := by rw [normalizedIncidence]; ring1
  refine
    { delta := delta
      lineAZero := directrixAZero
      conicDNonzero := conicDNonzero
      lineC := lineC
      normalizedFocusOff := normalizedFocusOff
      aNormalized := ?_
      bNormalized := ?_
      cNormalized := ?_ }
  · apply div_eq_of_eq_mul_right conicDNonzero
    calc
      conic.a = presentation.scale *
          (-2 * directrix.a * directrix.c -
            2 * lineNorm directrix * focus.x) := presentation.aEquation
      _ = conic.d * (-2 * focus.x) := by
        rw [presentation.dEquation]
        unfold lineNorm
        rw [directrixAZero]
        ring1
  · apply div_eq_of_eq_mul_right conicDNonzero
    calc
      conic.b = presentation.scale *
          (-2 * directrix.b * directrix.c -
            2 * lineNorm directrix * focus.y) := presentation.bEquation
      _ = conic.d * (-2 * delta - 2 * focus.y) := by
        rw [presentation.dEquation]
        unfold lineNorm
        rw [directrixAZero, lineC]
        ring1
  · apply div_eq_of_eq_mul_right conicDNonzero
    calc
      conic.c = presentation.scale *
          (lineNorm directrix * (focus.x ^ 2 + focus.y ^ 2) -
            directrix.c ^ 2) := presentation.cEquation
      _ = conic.d *
          (focus.x ^ 2 + focus.y ^ 2 - delta ^ 2) := by
        rw [presentation.dEquation]
        unfold lineNorm
        rw [directrixAZero, lineC]
        ring1

/-- Uniqueness of the recovered data in the `a = 0` chart. -/
private theorem parabolaBCharts_unique
    (conic : Conic K) (focus otherFocus : Point K)
    (directrix otherDirectrix : Line K) (twoNonzero : (2 : K) ≠ 0)
    (first : ParabolaBChart conic focus directrix)
    (second : ParabolaBChart conic otherFocus otherDirectrix) :
    focus = otherFocus ∧ first.delta = second.delta := by
  have xProductsEqual :
      (-2 : K) * focus.x = (-2 : K) * otherFocus.x := by
    calc
      (-2 : K) * focus.x = conic.a / conic.d :=
        first.aNormalized.symm
      _ = (-2 : K) * otherFocus.x := second.aNormalized
  have xEqual : focus.x = otherFocus.x :=
    eq_of_mul_eq_mul_left (negative_two_nonzero twoNonzero) xProductsEqual
  have sumProductsEqual :
      (-2 : K) * (focus.y + first.delta) =
        (-2 : K) * (otherFocus.y + second.delta) := by
    calc
      (-2 : K) * (focus.y + first.delta) = conic.b / conic.d := by
        rw [first.bNormalized]
        ring1
      _ = (-2 : K) * (otherFocus.y + second.delta) := by
        rw [second.bNormalized]
        ring1
  have sumEqual : focus.y + first.delta =
      otherFocus.y + second.delta :=
    eq_of_mul_eq_mul_left (negative_two_nonzero twoNonzero)
      sumProductsEqual
  have squareDifferenceEqual :
      focus.y ^ 2 - first.delta ^ 2 =
        otherFocus.y ^ 2 - second.delta ^ 2 := by
    calc
      focus.y ^ 2 - first.delta ^ 2 =
          conic.c / conic.d - focus.x ^ 2 := by
        rw [first.cNormalized]
        ring1
      _ = conic.c / conic.d - otherFocus.x ^ 2 := by rw [xEqual]
      _ = otherFocus.y ^ 2 - second.delta ^ 2 := by
        rw [second.cNormalized]
        ring1
  have differenceProductsEqual :
      (focus.y + first.delta) * (focus.y - first.delta) =
        (focus.y + first.delta) *
          (otherFocus.y - second.delta) := by
    calc
      (focus.y + first.delta) * (focus.y - first.delta) =
          focus.y ^ 2 - first.delta ^ 2 := by ring1
      _ = otherFocus.y ^ 2 - second.delta ^ 2 := squareDifferenceEqual
      _ = (otherFocus.y + second.delta) *
          (otherFocus.y - second.delta) := by ring1
      _ = (focus.y + first.delta) *
          (otherFocus.y - second.delta) := by rw [← sumEqual]
  have differenceEqual :
      focus.y - first.delta = otherFocus.y - second.delta :=
    eq_of_mul_eq_mul_left first.normalizedFocusOff differenceProductsEqual
  have yProductsEqual : (2 : K) * focus.y = 2 * otherFocus.y := by
    calc
      (2 : K) * focus.y =
          (focus.y + first.delta) + (focus.y - first.delta) := by ring1
      _ = (otherFocus.y + second.delta) +
          (otherFocus.y - second.delta) := by
        rw [sumEqual, differenceEqual]
      _ = 2 * otherFocus.y := by ring1
  have yEqual : focus.y = otherFocus.y :=
    eq_of_mul_eq_mul_left twoNonzero yProductsEqual
  have deltaEqual : first.delta = second.delta := by
    calc
      first.delta = (focus.y + first.delta) - focus.y := by ring1
      _ = (otherFocus.y + second.delta) - focus.y := by rw [sumEqual]
      _ = second.delta := by rw [yEqual]; ring1
  exact ⟨Point.ext xEqual yEqual, deltaEqual⟩

/-- Theorem 101 (Parabola uniqueness): the focus is equal as a point and the
two displayed directrix triples represent the same line. -/
theorem parabola_uniqueness [DecidableEq K] (conic : Conic K)
    (twoNonzero : (2 : K) ≠ 0)
    {focus otherFocus : Point K} {directrix otherDirectrix : Line K}
    (presentation : conic.IsParabolaPresentation focus directrix)
    (otherPresentation :
      conic.IsParabolaPresentation otherFocus otherDirectrix) :
    focus = otherFocus ∧ directrix.Equivalent otherDirectrix := by
  rcases presentation with ⟨presentation⟩
  rcases otherPresentation with ⟨otherPresentation⟩
  by_cases directrixAZero : directrix.a = 0
  · have conicFZero : conic.f = 0 := by
      calc
        conic.f = presentation.scale * directrix.a ^ 2 :=
          presentation.fEquation
        _ = 0 := by rw [directrixAZero]; ring1
    have otherDirectrixAZero : otherDirectrix.a = 0 := by
      by_cases otherDirectrixAZero : otherDirectrix.a = 0
      · exact otherDirectrixAZero
      · have otherASquareNonzero : otherDirectrix.a ^ 2 ≠ 0 := by
          simpa only [pow_two] using
            RFAP.ExplicitField.mul_ne_zero otherDirectrixAZero
              otherDirectrixAZero
        have productNonzero :
            otherPresentation.scale * otherDirectrix.a ^ 2 ≠ 0 :=
          RFAP.ExplicitField.mul_ne_zero otherPresentation.scaleNonzero
            otherASquareNonzero
        exact False.elim (productNonzero (by
          calc
            otherPresentation.scale * otherDirectrix.a ^ 2 = conic.f :=
              otherPresentation.fEquation.symm
            _ = 0 := conicFZero))
    let firstChart := parabolaBChart conic focus directrix presentation
      directrixAZero
    let secondChart := parabolaBChart conic otherFocus otherDirectrix
      otherPresentation otherDirectrixAZero
    rcases parabolaBCharts_unique conic focus otherFocus directrix
        otherDirectrix twoNonzero firstChart secondChart with
      ⟨focusEqual, deltaEqual⟩
    refine ⟨focusEqual, ?_⟩
    unfold Line.Equivalent
    constructor
    · rw [directrixAZero, otherDirectrixAZero]
      ring1
    · constructor
      · rw [directrixAZero, otherDirectrixAZero]
        ring1
      · calc
          directrix.b * otherDirectrix.c =
              directrix.b * (secondChart.delta * otherDirectrix.b) := by
            rw [secondChart.lineC]
          _ = directrix.b * (firstChart.delta * otherDirectrix.b) := by
            rw [deltaEqual]
          _ = otherDirectrix.b * directrix.c := by
            rw [firstChart.lineC]
            ring1
  · have otherDirectrixANonzero : otherDirectrix.a ≠ 0 := by
      have firstChart :=
        parabolaAChart conic focus directrix presentation directrixAZero
      by_cases otherDirectrixANonzero : otherDirectrix.a = 0
      · apply False.elim
        apply firstChart.conicFNonzero
        calc
          conic.f = otherPresentation.scale * otherDirectrix.a ^ 2 :=
            otherPresentation.fEquation
          _ = 0 := by rw [otherDirectrixANonzero]; ring1
      · exact otherDirectrixANonzero
    let firstChart :=
      parabolaAChart conic focus directrix presentation directrixAZero
    let secondChart :=
      parabolaAChart conic otherFocus otherDirectrix otherPresentation
        otherDirectrixANonzero
    rcases parabolaACharts_unique conic focus otherFocus directrix
        otherDirectrix twoNonzero firstChart secondChart with
      ⟨focusEqual, betaEqual, gammaEqual⟩
    refine ⟨focusEqual, ?_⟩
    unfold Line.Equivalent
    constructor
    · calc
        directrix.a * otherDirectrix.b =
            directrix.a * (secondChart.beta * otherDirectrix.a) := by
          rw [secondChart.lineB]
        _ = directrix.a * (firstChart.beta * otherDirectrix.a) := by
          rw [betaEqual]
        _ = otherDirectrix.a * directrix.b := by
          rw [firstChart.lineB]
          ring1
    · constructor
      · calc
          directrix.a * otherDirectrix.c =
              directrix.a * (secondChart.gamma * otherDirectrix.a) := by
            rw [secondChart.lineC]
          _ = directrix.a * (firstChart.gamma * otherDirectrix.a) := by
            rw [gammaEqual]
          _ = otherDirectrix.a * directrix.c := by
            rw [firstChart.lineC]
            ring1
      · calc
          directrix.b * otherDirectrix.c =
              (firstChart.beta * directrix.a) *
                (secondChart.gamma * otherDirectrix.a) := by
            rw [firstChart.lineB, secondChart.lineC]
          _ = (secondChart.beta * otherDirectrix.a) *
              (firstChart.gamma * directrix.a) := by
            rw [betaEqual, gammaEqual]
            ring1
          _ = otherDirectrix.b * directrix.c := by
            rw [secondChart.lineB, firstChart.lineC]

/-- Theorem 101 packaged as unique existence from the definition of parabola. -/
theorem parabola_has_unique_focus_directrix [DecidableEq K]
    (conic : Conic K) (twoNonzero : (2 : K) ≠ 0)
    (isParabola : conic.IsParabola) :
    ∃ focus : Point K, ∃ directrix : Line K,
      conic.IsParabolaPresentation focus directrix ∧
        ∀ otherFocus : Point K, ∀ otherDirectrix : Line K,
          conic.IsParabolaPresentation otherFocus otherDirectrix →
            otherFocus = focus ∧ otherDirectrix.Equivalent directrix := by
  rcases isParabola with ⟨focus, directrix, presentation⟩
  refine ⟨focus, directrix, presentation, ?_⟩
  intro otherFocus otherDirectrix otherPresentation
  exact parabola_uniqueness conic twoNonzero otherPresentation presentation

/-- The constructed conic has precisely the source equation
`Q(X,F) = Q(X,l)`. -/
theorem parabolaConic_contains_iff_equal_quadrances [DecidableEq K]
    (focus point : Point K) (directrix : Line K)
    (directrixNonNull : ¬ directrix.IsNull) :
    (parabolaConic focus directrix).Contains point ↔
      quadrance point focus =
        pointLineQuadrance point directrix directrixNonNull := by
  have normNonzero : lineNorm directrix ≠ 0 := directrixNonNull
  have normCancel :
      lineNorm directrix * (lineNorm directrix)⁻¹ = (1 : K) :=
    RFAP.ExplicitField.mul_inv_cancel _ normNonzero
  rw [Contains, parabolaConic_evaluate]
  rw [pointLineQuadrance_formula]
  simp only [RFAP.ExplicitField.div_eq_mul_inv]
  constructor
  · intro clearedEquation
    have scaledDifferenceZero :
        lineNorm directrix *
          (quadrance point focus -
            (directrix.a * point.x + directrix.b * point.y + directrix.c) ^ 2 *
              (lineNorm directrix)⁻¹) = 0 := by
      calc
        lineNorm directrix *
            (quadrance point focus -
              (directrix.a * point.x + directrix.b * point.y +
                  directrix.c) ^ 2 * (lineNorm directrix)⁻¹) =
          lineNorm directrix * quadrance point focus -
            (directrix.a * point.x + directrix.b * point.y +
                directrix.c) ^ 2 *
              (lineNorm directrix * (lineNorm directrix)⁻¹) := by ring1
        _ = 0 := by
          rw [normCancel]
          simpa only [mul_one] using clearedEquation
    have differenceZero :=
      eq_zero_of_mul_eq_zero_left normNonzero scaledDifferenceZero
    calc
      quadrance point focus =
          (quadrance point focus -
              (directrix.a * point.x + directrix.b * point.y +
                  directrix.c) ^ 2 * (lineNorm directrix)⁻¹) +
            (directrix.a * point.x + directrix.b * point.y +
                directrix.c) ^ 2 * (lineNorm directrix)⁻¹ := by ring1
      _ = (directrix.a * point.x + directrix.b * point.y +
          directrix.c) ^ 2 * (lineNorm directrix)⁻¹ := by
        rw [differenceZero]
        ring1
  · intro equality
    calc
      lineNorm directrix * quadrance point focus -
          (directrix.a * point.x + directrix.b * point.y + directrix.c) ^ 2 =
        lineNorm directrix *
            ((directrix.a * point.x + directrix.b * point.y +
                directrix.c) ^ 2 * (lineNorm directrix)⁻¹) -
          (directrix.a * point.x + directrix.b * point.y + directrix.c) ^ 2 := by
            rw [equality]
      _ = (directrix.a * point.x + directrix.b * point.y +
          directrix.c) ^ 2 *
            (lineNorm directrix * (lineNorm directrix)⁻¹ - 1) := by ring1
      _ = 0 := by rw [normCancel]; ring1

/-- Exercise 15.7: a parabola has no center.  The two putative center equations
combine to say that the focus lies on the directrix. -/
theorem parabola_has_no_center (conic : Conic K)
    (focus : Point K) (directrix : Line K)
    (twoNonzero : (2 : K) ≠ 0)
    (presentation : conic.IsParabolaPresentation focus directrix) :
    ¬ ∃ center : Point K, conic.IsCenter center := by
  rcases presentation with ⟨presentation⟩
  rintro ⟨center, firstCenterEquation, secondCenterEquation⟩
  have scaleTwoNonzero : presentation.scale * 2 ≠ 0 :=
    RFAP.ExplicitField.mul_ne_zero presentation.scaleNonzero twoNonzero
  have firstInnerZero :
      directrix.b ^ 2 * center.x -
          directrix.a * directrix.b * center.y -
          directrix.a * directrix.c -
          lineNorm directrix * focus.x = 0 := by
    apply eq_zero_of_mul_eq_zero_left scaleTwoNonzero
    calc
      presentation.scale * 2 *
          (directrix.b ^ 2 * center.x -
            directrix.a * directrix.b * center.y -
            directrix.a * directrix.c -
            lineNorm directrix * focus.x) =
        2 * conic.d * center.x + conic.e * center.y + conic.a := by
          rw [presentation.dEquation, presentation.eEquation,
            presentation.aEquation]
          ring1
      _ = 0 := firstCenterEquation
  have secondInnerZero :
      -directrix.a * directrix.b * center.x +
          directrix.a ^ 2 * center.y -
          directrix.b * directrix.c -
          lineNorm directrix * focus.y = 0 := by
    apply eq_zero_of_mul_eq_zero_left scaleTwoNonzero
    calc
      presentation.scale * 2 *
          (-directrix.a * directrix.b * center.x +
            directrix.a ^ 2 * center.y -
            directrix.b * directrix.c -
            lineNorm directrix * focus.y) =
        conic.e * center.x + 2 * conic.f * center.y + conic.b := by
          rw [presentation.eEquation, presentation.fEquation,
            presentation.bEquation]
          ring1
      _ = 0 := secondCenterEquation
  have incidenceScaledZero :
      lineNorm directrix *
        (directrix.a * focus.x + directrix.b * focus.y + directrix.c) = 0 := by
    calc
      lineNorm directrix *
          (directrix.a * focus.x + directrix.b * focus.y + directrix.c) =
        -(directrix.a *
            (directrix.b ^ 2 * center.x -
              directrix.a * directrix.b * center.y -
              directrix.a * directrix.c -
              lineNorm directrix * focus.x) +
          directrix.b *
            (-directrix.a * directrix.b * center.x +
              directrix.a ^ 2 * center.y -
              directrix.b * directrix.c -
              lineNorm directrix * focus.y)) := by
                unfold lineNorm
                ring1
      _ = 0 := by rw [firstInnerZero, secondInnerZero]; ring1
  have focusOnDirectrix : directrix.Contains focus := by
    exact eq_zero_of_mul_eq_zero_left presentation.directrixNonNull
      incidenceScaledZero
  exact presentation.focusNotOnDirectrix focusOnDirectrix

/-- Exercise 15.7 stated for every presented parabola. -/
theorem exercise_15_7 (conic : Conic K) (twoNonzero : (2 : K) ≠ 0)
    (isParabola : conic.IsParabola) :
    ¬ ∃ center : Point K, conic.IsCenter center := by
  rcases isParabola with ⟨focus, directrix, presentation⟩
  exact parabola_has_no_center conic focus directrix twoNonzero presentation

/-- The directrix `⟨1:0:a⟩` used in Example 15.3. -/
def example15ThreeDirectrix [Nontrivial K] (parameter : K) : Line K where
  a := 1
  b := 0
  c := parameter
  direction_nonzero := Or.inl one_ne_zero

/-- The displayed conic `⟨0:0:1:-4a:0:0⟩` in Example 15.3. -/
def example15ThreeConic [Nontrivial K] (parameter : K) : Conic K where
  d := 0
  e := 0
  f := 1
  a := -4 * parameter
  b := 0
  c := 0
  quadratic_nonzero := Or.inr (Or.inr one_ne_zero)

/-- Example 15.3: the displayed conic is presented by focus `[a,0]` and
directrix `⟨1:0:a⟩`. -/
theorem example_15_3 [Nontrivial K] (twoNonzero : (2 : K) ≠ 0)
    (parameter : K) (parameterNonzero : parameter ≠ 0) :
    (example15ThreeConic parameter).IsParabolaPresentation
      ⟨parameter, 0⟩ (example15ThreeDirectrix parameter) := by
  have twoParameterNonzero : 2 * parameter ≠ 0 :=
    RFAP.ExplicitField.mul_ne_zero twoNonzero parameterNonzero
  refine ⟨
    { directrixNonNull := ?_
      focusNotOnDirectrix := ?_
      scale := 1
      scaleNonzero := one_ne_zero
      dEquation := ?_
      eEquation := ?_
      fEquation := ?_
      aEquation := ?_
      bEquation := ?_
      cEquation := ?_ }⟩
  · unfold Line.IsNull example15ThreeDirectrix
    intro oneZero
    exact one_ne_zero (by simpa only [one_pow, zero_pow (by decide : 2 ≠ 0),
      add_zero] using oneZero)
  · unfold Line.Contains example15ThreeDirectrix
    intro incidence
    apply twoParameterNonzero
    calc
      2 * parameter =
          (1 : K) * parameter + 0 * 0 + parameter := by ring1
      _ = 0 := incidence
  all_goals dsimp only [example15ThreeConic, example15ThreeDirectrix]
  all_goals try unfold lineNorm
  all_goals ring1

/-- Example 15.3's equation is exactly `y² = 4ax`. -/
theorem example_15_3_equation [Nontrivial K]
    (parameter : K) (point : Point K) :
    (example15ThreeConic parameter).Contains point ↔
      point.y ^ 2 = 4 * parameter * point.x := by
  unfold Contains evaluate example15ThreeConic
  constructor <;> intro equation
  · calc
      point.y ^ 2 =
          (0 : K) * point.x ^ 2 + 0 * point.x * point.y +
            1 * point.y ^ 2 + (-4 * parameter) * point.x +
            0 * point.y + 0 + 4 * parameter * point.x := by ring1
      _ = 4 * parameter * point.x := by rw [equation]; ring1
  · calc
      (0 : K) * point.x ^ 2 + 0 * point.x * point.y +
          1 * point.y ^ 2 + (-4 * parameter) * point.x +
          0 * point.y + 0 =
        point.y ^ 2 - 4 * parameter * point.x := by ring1
      _ = 0 := by rw [equation]; ring1

/-- Example 15.4: over the executable eleven-element field, the focus `[1,0]`
and directrix `⟨1:0:1⟩` present the displayed parabola. -/
theorem example_15_4 :
    (example15ThreeConic (K := FieldEleven.Element) 1).IsParabolaPresentation
      ⟨1, 0⟩ (example15ThreeDirectrix 1) :=
  example_15_3 (K := FieldEleven.Element) (by decide) 1 (by decide)

/-- Example 15.4's plotted finite-field conic has equation `y² = 4x`. -/
theorem example_15_4_equation (point : Point FieldEleven.Element) :
    (example15ThreeConic (K := FieldEleven.Element) 1).Contains point ↔
      point.y ^ 2 = 4 * point.x := by
  have coefficient :
      (4 : FieldEleven.Element) * (1 : FieldEleven.Element) = 4 := by decide
  constructor
  · intro onConic
    have equation :=
      (example_15_3_equation (K := FieldEleven.Element) 1 point).1 onConic
    calc
      point.y ^ 2 = 4 * (1 : FieldEleven.Element) * point.x := equation
      _ = 4 * point.x := by rw [coefficient]
  · intro equation
    apply (example_15_3_equation (K := FieldEleven.Element) 1 point).2
    calc
      point.y ^ 2 = 4 * point.x := equation
      _ = 4 * (1 : FieldEleven.Element) * point.x := by rw [coefficient]

end Conic

end DivineProportions
