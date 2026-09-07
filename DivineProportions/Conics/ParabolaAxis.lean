import DivineProportions.Conics.Axis
import DivineProportions.Conics.Parabola
import DivineProportions.Isometries.CentralReflection
import DivineProportions.Isometries.Models
import DivineProportions.Plane.LineReflection

/-!
# Divine Proportions, Exercises 15.8 and 15.9

This module constructs a parabola's axis from its focus and directrix, proves
that equation preservation characterizes that axis up to the project's
quotient-free line equivalence, and constructs the unique vertex as the
midpoint of the focus and its altitude foot on the directrix.
-/

namespace DivineProportions

variable {K : Type*} [RFAP.ExplicitField K]

namespace Conic

/-- Evaluation of a displayed line's affine polynomial. -/
def lineValue (line : Line K) (point : Point K) : K :=
  line.a * point.x + line.b * point.y + line.c

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

/-- Multiply every displayed conic coefficient by one explicit nonzero scale. -/
def scaleConic (scale : K) (scaleNonzero : scale ≠ 0)
    (conic : Conic K) : Conic K where
  d := scale * conic.d
  e := scale * conic.e
  f := scale * conic.f
  a := scale * conic.a
  b := scale * conic.b
  c := scale * conic.c
  quadratic_nonzero := by
    rcases conic.quadratic_nonzero with dNonzero | eNonzero | fNonzero
    · exact Or.inl (RFAP.ExplicitField.mul_ne_zero scaleNonzero dNonzero)
    · exact Or.inr (Or.inl
        (RFAP.ExplicitField.mul_ne_zero scaleNonzero eNonzero))
    · exact Or.inr (Or.inr
        (RFAP.ExplicitField.mul_ne_zero scaleNonzero fNonzero))

/-- Scaling coefficients scales the evaluated polynomial by the same factor. -/
theorem scaleConic_evaluate (scale : K) (scaleNonzero : scale ≠ 0)
    (conic : Conic K) (point : Point K) :
    (scaleConic scale scaleNonzero conic).evaluate point =
      scale * conic.evaluate point := by
  unfold scaleConic evaluate
  ring1

/-- Six finite probes recover all coefficients of a quadratic polynomial in
two variables when characteristic two is excluded. -/
theorem coefficients_eq_of_evaluate_eq (left right : Conic K)
    (twoNonzero : (2 : K) ≠ 0)
    (evaluationsEqual : ∀ point : Point K,
      left.evaluate point = right.evaluate point) :
    left.d = right.d ∧ left.e = right.e ∧ left.f = right.f ∧
      left.a = right.a ∧ left.b = right.b ∧ left.c = right.c := by
  have atOrigin := evaluationsEqual (⟨0, 0⟩ : Point K)
  have atPositiveX := evaluationsEqual (⟨1, 0⟩ : Point K)
  have atNegativeX := evaluationsEqual (⟨-1, 0⟩ : Point K)
  have atPositiveY := evaluationsEqual (⟨0, 1⟩ : Point K)
  have atNegativeY := evaluationsEqual (⟨0, -1⟩ : Point K)
  have atOneOne := evaluationsEqual (⟨1, 1⟩ : Point K)
  have cEqual : left.c = right.c := by
    simpa only [evaluate, mul_zero, zero_pow (by decide : 2 ≠ 0),
      zero_mul, add_zero, zero_add] using atOrigin
  have dProductsEqual : (2 : K) * left.d = 2 * right.d := by
    calc
      (2 : K) * left.d =
          left.evaluate ⟨1, 0⟩ + left.evaluate ⟨-1, 0⟩ -
            2 * left.evaluate ⟨0, 0⟩ := by
              unfold evaluate
              ring1
      _ = right.evaluate ⟨1, 0⟩ + right.evaluate ⟨-1, 0⟩ -
            2 * right.evaluate ⟨0, 0⟩ := by
              rw [atPositiveX, atNegativeX, atOrigin]
      _ = 2 * right.d := by
        unfold evaluate
        ring1
  have dEqual : left.d = right.d :=
    eq_of_mul_eq_mul_left twoNonzero dProductsEqual
  have aProductsEqual : (2 : K) * left.a = 2 * right.a := by
    calc
      (2 : K) * left.a =
          left.evaluate ⟨1, 0⟩ - left.evaluate ⟨-1, 0⟩ := by
            unfold evaluate
            ring1
      _ = right.evaluate ⟨1, 0⟩ - right.evaluate ⟨-1, 0⟩ := by
        rw [atPositiveX, atNegativeX]
      _ = 2 * right.a := by
        unfold evaluate
        ring1
  have aEqual : left.a = right.a :=
    eq_of_mul_eq_mul_left twoNonzero aProductsEqual
  have fProductsEqual : (2 : K) * left.f = 2 * right.f := by
    calc
      (2 : K) * left.f =
          left.evaluate ⟨0, 1⟩ + left.evaluate ⟨0, -1⟩ -
            2 * left.evaluate ⟨0, 0⟩ := by
              unfold evaluate
              ring1
      _ = right.evaluate ⟨0, 1⟩ + right.evaluate ⟨0, -1⟩ -
            2 * right.evaluate ⟨0, 0⟩ := by
              rw [atPositiveY, atNegativeY, atOrigin]
      _ = 2 * right.f := by
        unfold evaluate
        ring1
  have fEqual : left.f = right.f :=
    eq_of_mul_eq_mul_left twoNonzero fProductsEqual
  have bProductsEqual : (2 : K) * left.b = 2 * right.b := by
    calc
      (2 : K) * left.b =
          left.evaluate ⟨0, 1⟩ - left.evaluate ⟨0, -1⟩ := by
            unfold evaluate
            ring1
      _ = right.evaluate ⟨0, 1⟩ - right.evaluate ⟨0, -1⟩ := by
        rw [atPositiveY, atNegativeY]
      _ = 2 * right.b := by
        unfold evaluate
        ring1
  have bEqual : left.b = right.b :=
    eq_of_mul_eq_mul_left twoNonzero bProductsEqual
  have eEqual : left.e = right.e := by
    calc
      left.e = left.evaluate ⟨1, 1⟩ -
          (left.d + left.f + left.a + left.b + left.c) := by
            unfold evaluate
            ring1
      _ = right.evaluate ⟨1, 1⟩ -
          (right.d + right.f + right.a + right.b + right.c) := by
            rw [atOneOne, dEqual, fEqual, aEqual, bEqual, cEqual]
      _ = right.e := by
        unfold evaluate
        ring1
  exact ⟨dEqual, eEqual, fEqual, aEqual, bEqual, cEqual⟩

/-- A scaled parabola presentation evaluates as its scale times the canonical
focus/directrix conic. -/
theorem ParabolaPresentationData.evaluate_eq_scale_mul [DecidableEq K]
    {conic : Conic K} {focus : Point K} {directrix : Line K}
    (presentation : ParabolaPresentationData conic focus directrix)
    (point : Point K) :
    conic.evaluate point =
      presentation.scale * (parabolaConic focus directrix).evaluate point := by
  unfold evaluate parabolaConic
  rw [presentation.dEquation, presentation.eEquation,
    presentation.fEquation, presentation.aEquation,
    presentation.bEquation, presentation.cEquation]
  unfold lineNorm
  ring1

/-- The reflected-line polynomial at a reflected point is the original line
polynomial multiplied by the negative mirror norm. -/
theorem reflectLine_lineValue_reflectPoint [DecidableEq K]
    (mirror target : Line K) (mirrorNonNull : ¬ mirror.IsNull)
    (point : Point K) :
    lineValue (reflectLine mirror target mirrorNonNull)
        (reflectPoint mirror mirrorNonNull point) =
      -lineNorm mirror * lineValue target point := by
  have normCancel : lineNorm mirror * (lineNorm mirror)⁻¹ = (1 : K) :=
    RFAP.ExplicitField.mul_inv_cancel _ mirrorNonNull
  rw [reflectPoint_formula]
  unfold lineValue reflectLine
  change
    reflectedLineA mirror target *
          (((mirror.b ^ 2 - mirror.a ^ 2) * point.x -
            2 * mirror.a * mirror.b * point.y -
            2 * mirror.a * mirror.c) / lineNorm mirror) +
        reflectedLineB mirror target *
          ((-2 * mirror.a * mirror.b * point.x +
            (mirror.a ^ 2 - mirror.b ^ 2) * point.y -
            2 * mirror.b * mirror.c) / lineNorm mirror) +
        reflectedLineC mirror target =
      -lineNorm mirror *
        (target.a * point.x + target.b * point.y + target.c)
  simp only [RFAP.ExplicitField.div_eq_mul_inv]
  calc
    reflectedLineA mirror target *
          (((mirror.b ^ 2 - mirror.a ^ 2) * point.x -
            2 * mirror.a * mirror.b * point.y -
            2 * mirror.a * mirror.c) * (lineNorm mirror)⁻¹) +
        reflectedLineB mirror target *
          ((-2 * mirror.a * mirror.b * point.x +
            (mirror.a ^ 2 - mirror.b ^ 2) * point.y -
            2 * mirror.b * mirror.c) * (lineNorm mirror)⁻¹) +
        reflectedLineC mirror target =
      -lineNorm mirror * (target.a * point.x + target.b * point.y) *
          (lineNorm mirror * (lineNorm mirror)⁻¹) +
        2 * mirror.c *
          (mirror.a * target.a + mirror.b * target.b) *
          (1 - lineNorm mirror * (lineNorm mirror)⁻¹) -
        lineNorm mirror * target.c := by
          unfold reflectedLineA reflectedLineB reflectedLineC lineNorm
          ring1
    _ = -lineNorm mirror *
        (target.a * point.x + target.b * point.y + target.c) := by
      rw [normCancel]
      ring1

/-- Reflecting in a line perpendicular to a target preserves the target's
affine line polynomial exactly. -/
theorem lineValue_reflectPoint_of_perpendicular
    (mirror target : Line K) (mirrorNonNull : ¬ mirror.IsNull)
    (perpendicular : mirror.Perpendicular target) (point : Point K) :
    lineValue target (reflectPoint mirror mirrorNonNull point) =
      lineValue target point := by
  have normCancel : lineNorm mirror * (lineNorm mirror)⁻¹ = (1 : K) :=
    RFAP.ExplicitField.mul_inv_cancel _ mirrorNonNull
  rw [reflectPoint_formula]
  unfold lineValue reflectionFormula
  simp only [RFAP.ExplicitField.div_eq_mul_inv]
  calc
    target.a *
          (((mirror.b ^ 2 - mirror.a ^ 2) * point.x -
            2 * mirror.a * mirror.b * point.y -
            2 * mirror.a * mirror.c) * (lineNorm mirror)⁻¹) +
        target.b *
          ((-2 * mirror.a * mirror.b * point.x +
            (mirror.a ^ 2 - mirror.b ^ 2) * point.y -
            2 * mirror.b * mirror.c) * (lineNorm mirror)⁻¹) +
        target.c =
      (target.a * point.x + target.b * point.y + target.c) *
          (lineNorm mirror * (lineNorm mirror)⁻¹) -
        2 * (mirror.a * target.a + mirror.b * target.b) *
          (mirror.a * point.x + mirror.b * point.y + mirror.c) *
          (lineNorm mirror)⁻¹ +
        target.c * (1 - lineNorm mirror * (lineNorm mirror)⁻¹) := by
          unfold lineNorm
          ring1
    _ = target.a * point.x + target.b * point.y + target.c := by
      unfold Line.Perpendicular at perpendicular
      rw [normCancel, perpendicular]
      ring1

/-- Simultaneously reflecting the focus and directrix multiplies the canonical
parabola polynomial by the square of the mirror norm. -/
theorem parabolaConic_reflected_evaluate [DecidableEq K]
    (focus point : Point K) (directrix mirror : Line K)
    (mirrorNonNull : ¬ mirror.IsNull) :
    (parabolaConic (reflectPoint mirror mirrorNonNull focus)
        (reflectLine mirror directrix mirrorNonNull)).evaluate point =
      lineNorm mirror ^ 2 *
        (parabolaConic focus directrix).evaluate
          (reflectPoint mirror mirrorNonNull point) := by
  have quadranceReflected :
      quadrance point (reflectPoint mirror mirrorNonNull focus) =
        quadrance (reflectPoint mirror mirrorNonNull point) focus := by
    calc
      quadrance point (reflectPoint mirror mirrorNonNull focus) =
          quadrance (reflectPoint mirror mirrorNonNull point)
            (reflectPoint mirror mirrorNonNull
              (reflectPoint mirror mirrorNonNull focus)) :=
        (reflectPoint_preserves_quadrance mirror mirrorNonNull point
          (reflectPoint mirror mirrorNonNull focus)).symm
      _ = quadrance (reflectPoint mirror mirrorNonNull point) focus := by
        rw [reflectPoint_involutive]
  have reflectedValue :
      lineValue (reflectLine mirror directrix mirrorNonNull) point =
        -lineNorm mirror *
          lineValue directrix (reflectPoint mirror mirrorNonNull point) := by
    calc
      lineValue (reflectLine mirror directrix mirrorNonNull) point =
          lineValue (reflectLine mirror directrix mirrorNonNull)
            (reflectPoint mirror mirrorNonNull
              (reflectPoint mirror mirrorNonNull point)) := by
                rw [reflectPoint_involutive]
      _ = -lineNorm mirror *
          lineValue directrix (reflectPoint mirror mirrorNonNull point) :=
        reflectLine_lineValue_reflectPoint mirror directrix mirrorNonNull
          (reflectPoint mirror mirrorNonNull point)
  rw [parabolaConic_evaluate, parabolaConic_evaluate,
    reflectLine_norm, quadranceReflected]
  change
    lineNorm mirror ^ 2 * lineNorm directrix *
          quadrance (reflectPoint mirror mirrorNonNull point) focus -
        lineValue (reflectLine mirror directrix mirrorNonNull) point ^ 2 =
      lineNorm mirror ^ 2 *
        (lineNorm directrix *
            quadrance (reflectPoint mirror mirrorNonNull point) focus -
          lineValue directrix
            (reflectPoint mirror mirrorNonNull point) ^ 2)
  rw [reflectedValue]
  ring1

/-- Incidence with any scaled presentation is exactly equality of quadrance
to the focus and quadrance to the directrix. -/
theorem contains_iff_equal_quadrances_of_presentation [DecidableEq K]
    {conic : Conic K} {focus point : Point K} {directrix : Line K}
    (presentation : ParabolaPresentationData conic focus directrix) :
    conic.Contains point ↔
      quadrance point focus =
        pointLineQuadrance point directrix presentation.directrixNonNull := by
  have canonicalEquivalence :=
    parabolaConic_contains_iff_equal_quadrances focus point directrix
      presentation.directrixNonNull
  constructor
  · intro contains
    have scaledZero :
        presentation.scale *
          (parabolaConic focus directrix).evaluate point = 0 := by
      calc
        presentation.scale *
            (parabolaConic focus directrix).evaluate point =
          conic.evaluate point :=
            (presentation.evaluate_eq_scale_mul point).symm
        _ = 0 := contains
    have canonicalContains :
        (parabolaConic focus directrix).Contains point :=
      eq_zero_of_mul_eq_zero_left presentation.scaleNonzero scaledZero
    exact canonicalEquivalence.1 canonicalContains
  · intro equalQuadrances
    have canonicalContains :
        (parabolaConic focus directrix).Contains point :=
      canonicalEquivalence.2 equalQuadrances
    unfold Contains at canonicalContains ⊢
    rw [presentation.evaluate_eq_scale_mul, canonicalContains]
    ring1

/-- The canonical parabola axis is the altitude from the focus to the
directrix. -/
def parabolaAxis (focus : Point K) (directrix : Line K) : Line K :=
  altitudeThrough focus directrix

/-- A non-null directrix gives a non-null canonical axis. -/
theorem parabolaAxis_nonNull (focus : Point K) (directrix : Line K)
    (directrixNonNull : ¬ directrix.IsNull) :
    ¬ (parabolaAxis focus directrix).IsNull := by
  intro axisNull
  apply directrixNonNull
  unfold Line.IsNull at axisNull ⊢
  unfold parabolaAxis altitudeThrough at axisNull
  calc
    directrix.a ^ 2 + directrix.b ^ 2 =
        (-directrix.b) ^ 2 + directrix.a ^ 2 := by ring1
    _ = 0 := axisNull

/-- The canonical axis contains the focus. -/
theorem parabolaAxis_contains_focus (focus : Point K)
    (directrix : Line K) :
    (parabolaAxis focus directrix).Contains focus := by
  exact altitudeThrough_contains focus directrix

/-- The canonical axis is perpendicular to the directrix. -/
theorem parabolaAxis_perpendicular (focus : Point K)
    (directrix : Line K) :
    (parabolaAxis focus directrix).Perpendicular directrix := by
  exact altitudeThrough_perpendicular focus directrix

/-- Reflection in the focus altitude preserves the presented parabola
equation pointwise. -/
theorem parabolaAxis_isAxis [DecidableEq K]
    (conic : Conic K) (focus : Point K) (directrix : Line K)
    (presentation : ParabolaPresentationData conic focus directrix) :
    conic.IsAxis (parabolaAxis focus directrix) := by
  let axis := parabolaAxis focus directrix
  have axisNonNull : ¬ axis.IsNull :=
    parabolaAxis_nonNull focus directrix presentation.directrixNonNull
  have focusFixed :
      reflectPoint axis axisNonNull focus = focus :=
    reflectPoint_fixed_of_contains axis axisNonNull focus
      (parabolaAxis_contains_focus focus directrix)
  have perpendicular : axis.Perpendicular directrix :=
    parabolaAxis_perpendicular focus directrix
  refine ⟨axisNonNull, ?_⟩
  intro point
  rw [presentation.evaluate_eq_scale_mul,
    presentation.evaluate_eq_scale_mul]
  congr 1
  rw [parabolaConic_evaluate, parabolaConic_evaluate]
  have focusQuadrance :
      quadrance (reflectPoint axis axisNonNull point) focus =
        quadrance point focus := by
    calc
      quadrance (reflectPoint axis axisNonNull point) focus =
          quadrance (reflectPoint axis axisNonNull point)
            (reflectPoint axis axisNonNull focus) := by rw [focusFixed]
      _ = quadrance point focus :=
        reflectPoint_preserves_quadrance axis axisNonNull point focus
  have directrixValue :
      lineValue directrix (reflectPoint axis axisNonNull point) =
        lineValue directrix point :=
    lineValue_reflectPoint_of_perpendicular axis directrix axisNonNull
      perpendicular point
  change
    lineNorm directrix *
          quadrance (reflectPoint axis axisNonNull point) focus -
        lineValue directrix (reflectPoint axis axisNonNull point) ^ 2 =
      lineNorm directrix * quadrance point focus -
        lineValue directrix point ^ 2
  rw [focusQuadrance, directrixValue]

/-- An equation-preserving reflection turns a displayed focus/directrix pair
into another valid presentation of the same conic.  The new coefficient scale
is the old scale divided by the square of the mirror norm. -/
theorem reflectedPresentation_of_axis [DecidableEq K]
    (conic : Conic K) (focus : Point K) (directrix axis : Line K)
    (presentation : ParabolaPresentationData conic focus directrix)
    (twoNonzero : (2 : K) ≠ 0) (axisNonNull : ¬ axis.IsNull)
    (equationInvariant : ∀ point : Point K,
      conic.evaluate (reflectPoint axis axisNonNull point) =
        conic.evaluate point) :
    conic.IsParabolaPresentation
      (reflectPoint axis axisNonNull focus)
      (reflectLine axis directrix axisNonNull) := by
  let reflectedFocus := reflectPoint axis axisNonNull focus
  let reflectedDirectrix := reflectLine axis directrix axisNonNull
  have normNonzero : lineNorm axis ≠ 0 := axisNonNull
  have normSquareNonzero : lineNorm axis ^ 2 ≠ 0 := by
    simpa only [pow_two] using
      RFAP.ExplicitField.mul_ne_zero normNonzero normNonzero
  let reflectedScale := presentation.scale / lineNorm axis ^ 2
  have reflectedScaleNonzero : reflectedScale ≠ 0 := by
    exact RFAP.ExplicitField.div_ne_zero presentation.scaleNonzero
      normSquareNonzero
  have canonicalInvariant (point : Point K) :
      (parabolaConic focus directrix).evaluate
          (reflectPoint axis axisNonNull point) =
        (parabolaConic focus directrix).evaluate point := by
    apply eq_of_mul_eq_mul_left presentation.scaleNonzero
    calc
      presentation.scale *
          (parabolaConic focus directrix).evaluate
            (reflectPoint axis axisNonNull point) =
        conic.evaluate (reflectPoint axis axisNonNull point) :=
          (presentation.evaluate_eq_scale_mul
            (reflectPoint axis axisNonNull point)).symm
      _ = conic.evaluate point := equationInvariant point
      _ = presentation.scale *
          (parabolaConic focus directrix).evaluate point :=
        presentation.evaluate_eq_scale_mul point
  have reflectedDirectrixNonNull : ¬ reflectedDirectrix.IsNull := by
    exact reflectLine_nonNull axis directrix axisNonNull
      presentation.directrixNonNull
  have reflectedFocusNotOnDirectrix :
      ¬ reflectedDirectrix.Contains reflectedFocus := by
    intro reflectedContains
    have scaledOriginalZero :
        -lineNorm axis * lineValue directrix focus = 0 := by
      calc
        -lineNorm axis * lineValue directrix focus =
            lineValue reflectedDirectrix reflectedFocus := by
              exact (reflectLine_lineValue_reflectPoint axis directrix
                axisNonNull focus).symm
        _ = 0 := reflectedContains
    have negativeNormNonzero : -lineNorm axis ≠ 0 := by
      intro negativeNormZero
      apply normNonzero
      calc
        lineNorm axis = -(-lineNorm axis) := by ring1
        _ = 0 := by rw [negativeNormZero]; ring1
    have originalZero : lineValue directrix focus = 0 :=
      eq_zero_of_mul_eq_zero_left negativeNormNonzero scaledOriginalZero
    apply presentation.focusNotOnDirectrix
    exact originalZero
  let scaledReflectedConic :=
    scaleConic reflectedScale reflectedScaleNonzero
      (parabolaConic reflectedFocus reflectedDirectrix)
  have scaleCancel :
      reflectedScale * lineNorm axis ^ 2 = presentation.scale := by
    unfold reflectedScale
    exact RFAP.ExplicitField.div_mul_cancel presentation.scale
      normSquareNonzero
  have evaluationsEqual (point : Point K) :
      conic.evaluate point = scaledReflectedConic.evaluate point := by
    calc
      conic.evaluate point = presentation.scale *
          (parabolaConic focus directrix).evaluate point :=
        presentation.evaluate_eq_scale_mul point
      _ = presentation.scale *
          (parabolaConic focus directrix).evaluate
            (reflectPoint axis axisNonNull point) := by
              rw [canonicalInvariant]
      _ = reflectedScale *
          (lineNorm axis ^ 2 *
            (parabolaConic focus directrix).evaluate
              (reflectPoint axis axisNonNull point)) := by
                rw [← scaleCancel]
                ring1
      _ = reflectedScale *
          (parabolaConic reflectedFocus reflectedDirectrix).evaluate point := by
            unfold reflectedFocus reflectedDirectrix
            rw [parabolaConic_reflected_evaluate]
      _ = scaledReflectedConic.evaluate point := by
        exact (scaleConic_evaluate reflectedScale reflectedScaleNonzero
          (parabolaConic reflectedFocus reflectedDirectrix) point).symm
  rcases coefficients_eq_of_evaluate_eq conic scaledReflectedConic
      twoNonzero evaluationsEqual with
    ⟨dEqual, eEqual, fEqual, aEqual, bEqual, cEqual⟩
  refine ⟨
    { directrixNonNull := reflectedDirectrixNonNull
      focusNotOnDirectrix := reflectedFocusNotOnDirectrix
      scale := reflectedScale
      scaleNonzero := reflectedScaleNonzero
      dEquation := ?_
      eEquation := ?_
      fEquation := ?_
      aEquation := ?_
      bEquation := ?_
      cEquation := ?_ }⟩
  · simpa only [scaledReflectedConic, scaleConic, parabolaConic] using dEqual
  · simpa only [scaledReflectedConic, scaleConic, parabolaConic] using eEqual
  · simpa only [scaledReflectedConic, scaleConic, parabolaConic] using fEqual
  · simpa only [scaledReflectedConic, scaleConic, parabolaConic] using aEqual
  · simpa only [scaledReflectedConic, scaleConic, parabolaConic] using bEqual
  · simpa only [scaledReflectedConic, scaleConic, parabolaConic] using cEqual

/-- A target parallel to a non-null mirror can be fixed by reflection only by
coinciding with that mirror.  Characteristic two is the sole cancellation
excluded by the affine-offset calculation. -/
theorem equivalent_of_parallel_and_reflectLine_fixed [DecidableEq K]
    (mirror target : Line K) (mirrorNonNull : ¬ mirror.IsNull)
    (twoNonzero : (2 : K) ≠ 0) (parallel : mirror.Parallel target)
    (fixed : (reflectLine mirror target mirrorNonNull).Equivalent target) :
    mirror.Equivalent target := by
  rcases direction_scale_of_parallel mirror target parallel with
    ⟨scale, scaleNonzero, targetA, targetB⟩
  have normNonzero : lineNorm mirror ≠ 0 := mirrorNonNull
  have reflectedA :
      reflectedLineA mirror target = lineNorm mirror * target.a := by
    unfold reflectedLineA lineNorm
    rw [targetA, targetB]
    ring1
  have reflectedB :
      reflectedLineB mirror target = lineNorm mirror * target.b := by
    unfold reflectedLineB lineNorm
    rw [targetA, targetB]
    ring1
  have reflectedC :
      reflectedLineC mirror target =
        lineNorm mirror * (2 * scale * mirror.c - target.c) := by
    unfold reflectedLineC lineNorm
    rw [targetA, targetB]
    ring1
  have targetC : target.c = scale * mirror.c := by
    rcases target.direction_nonzero with targetANonzero | targetBNonzero
    · have constantEquation :
          reflectedLineA mirror target * target.c =
            target.a * reflectedLineC mirror target := fixed.2.1
      rw [reflectedA, reflectedC] at constantEquation
      have factorNonzero : 2 * lineNorm mirror * target.a ≠ 0 :=
        RFAP.ExplicitField.mul_ne_zero
          (RFAP.ExplicitField.mul_ne_zero twoNonzero normNonzero)
          targetANonzero
      apply eq_of_mul_eq_mul_left factorNonzero
      calc
        (2 * lineNorm mirror * target.a) * target.c =
            lineNorm mirror * target.a * target.c +
              lineNorm mirror * target.a * target.c := by ring1
        _ = target.a *
              (lineNorm mirror * (2 * scale * mirror.c - target.c)) +
            lineNorm mirror * target.a * target.c := by
              rw [constantEquation]
        _ = (2 * lineNorm mirror * target.a) *
            (scale * mirror.c) := by ring1
    · have constantEquation :
          reflectedLineB mirror target * target.c =
            target.b * reflectedLineC mirror target := fixed.2.2
      rw [reflectedB, reflectedC] at constantEquation
      have factorNonzero : 2 * lineNorm mirror * target.b ≠ 0 :=
        RFAP.ExplicitField.mul_ne_zero
          (RFAP.ExplicitField.mul_ne_zero twoNonzero normNonzero)
          targetBNonzero
      apply eq_of_mul_eq_mul_left factorNonzero
      calc
        (2 * lineNorm mirror * target.b) * target.c =
            lineNorm mirror * target.b * target.c +
              lineNorm mirror * target.b * target.c := by ring1
        _ = target.b *
              (lineNorm mirror * (2 * scale * mirror.c - target.c)) +
            lineNorm mirror * target.b * target.c := by
              rw [constantEquation]
        _ = (2 * lineNorm mirror * target.b) *
            (scale * mirror.c) := by ring1
  unfold Line.Equivalent
  rw [targetA, targetB, targetC]
  constructor
  · ring1
  constructor <;> ring1

/-- Every equation-preserving mirror of a presented parabola is equivalent to
the focus altitude. -/
theorem parabolaAxis_unique [DecidableEq K]
    (conic : Conic K) (focus : Point K) (directrix axis : Line K)
    (presentation : ParabolaPresentationData conic focus directrix)
    (twoNonzero : (2 : K) ≠ 0) (isAxis : conic.IsAxis axis) :
    axis.Equivalent (parabolaAxis focus directrix) := by
  rcases isAxis with ⟨axisNonNull, equationInvariant⟩
  have reflectedPresentation :=
    reflectedPresentation_of_axis conic focus directrix axis presentation
      twoNonzero axisNonNull equationInvariant
  have reflectedUniqueness :=
    parabola_uniqueness conic twoNonzero reflectedPresentation
      ⟨presentation⟩
  have focusFixed : reflectPoint axis axisNonNull focus = focus :=
    reflectedUniqueness.1
  have axisContainsFocus : axis.Contains focus :=
    (reflectPoint_fixed_iff_contains axis axisNonNull twoNonzero focus).1
      focusFixed
  have fixedDirectrix :
      (reflectLine axis directrix axisNonNull).Equivalent directrix :=
    reflectedUniqueness.2
  have fixedDirection :
      directrix.Parallel (reflectLine axis directrix axisNonNull) :=
    line_parallel_of_equivalent (Line.equivalent_symm fixedDirectrix)
  have directionCases :=
    parallel_or_perpendicular_of_parallel_reflectLine axis directrix
      axisNonNull twoNonzero fixedDirection
  have axisPerpendicular : axis.Perpendicular directrix := by
    rcases directionCases with directrixParallel | directrixPerpendicular
    · have axisParallel : axis.Parallel directrix :=
        Line.parallel_symm directrixParallel
      have axisEquivalentDirectrix :=
        equivalent_of_parallel_and_reflectLine_fixed axis directrix
          axisNonNull twoNonzero axisParallel fixedDirectrix
      have focusOnDirectrix : directrix.Contains focus :=
        line_contains_of_equivalent axisEquivalentDirectrix focus
          axisContainsFocus
      exact False.elim
        (presentation.focusNotOnDirectrix focusOnDirectrix)
    · exact Line.perpendicular_symm directrixPerpendicular
  have canonicalParallel :
      (parabolaAxis focus directrix).Parallel axis := by
    unfold parabolaAxis altitudeThrough Line.Parallel
    unfold Line.Perpendicular at axisPerpendicular
    calc
      -directrix.b * axis.b - axis.a * directrix.a =
          -(axis.a * directrix.a + axis.b * directrix.b) := by ring1
      _ = 0 := by rw [axisPerpendicular]; ring1
  have canonicalEquivalentAxis :=
    line_equivalent_of_parallel_and_common_point
      (parabolaAxis focus directrix) axis focus canonicalParallel
      (parabolaAxis_contains_focus focus directrix) axisContainsFocus
  exact Line.equivalent_symm canonicalEquivalentAxis

/-- Exercise 15.8: every presented parabola has exactly one axis up to
quotient-free line equivalence, namely the altitude from its focus to its
directrix. -/
theorem exercise_15_8 [DecidableEq K] (conic : Conic K)
    (twoNonzero : (2 : K) ≠ 0) (isParabola : conic.IsParabola) :
    ∃ focus : Point K, ∃ directrix : Line K,
      conic.IsParabolaPresentation focus directrix ∧
        conic.IsAxis (parabolaAxis focus directrix) ∧
        ∀ otherAxis : Line K, conic.IsAxis otherAxis →
          otherAxis.Equivalent (parabolaAxis focus directrix) := by
  rcases isParabola with ⟨focus, directrix, presentation⟩
  rcases presentation with ⟨presentation⟩
  refine ⟨focus, directrix, ⟨presentation⟩, ?_, ?_⟩
  · exact parabolaAxis_isAxis conic focus directrix presentation
  · intro otherAxis otherIsAxis
    exact parabolaAxis_unique conic focus directrix otherAxis presentation
      twoNonzero otherIsAxis

/-- The vertex candidate is the midpoint of the focus and its altitude foot
on the directrix. -/
def parabolaVertex (focus : Point K) (directrix : Line K)
    (directrixNonNull : ¬ directrix.IsNull) : Point K :=
  midpoint focus (altitudeFoot focus directrix directrixNonNull)

/-- The focus does not coincide with its directrix foot in a valid parabola
presentation. -/
theorem focus_ne_directrixFoot
    {conic : Conic K} {focus : Point K} {directrix : Line K}
    (presentation : ParabolaPresentationData conic focus directrix) :
    focus ≠ altitudeFoot focus directrix presentation.directrixNonNull := by
  intro focusEqualsFoot
  apply presentation.focusNotOnDirectrix
  rw [focusEqualsFoot]
  exact altitudeFoot_on_line focus directrix presentation.directrixNonNull

/-- Every point on the focus altitude has the same directrix foot as the
focus itself. -/
theorem altitudeFoot_eq_focusFoot_of_on_parabolaAxis
    (focus point : Point K) (directrix : Line K)
    (directrixNonNull : ¬ directrix.IsNull)
    (onAxis : (parabolaAxis focus directrix).Contains point) :
    altitudeFoot point directrix directrixNonNull =
      altitudeFoot focus directrix directrixNonNull := by
  let focusFoot := altitudeFoot focus directrix directrixNonNull
  have focusFootOnDirectrix : directrix.Contains focusFoot :=
    altitudeFoot_on_line focus directrix directrixNonNull
  have focusFootOnAxis :
      (parabolaAxis focus directrix).Contains focusFoot := by
    exact altitudeFoot_on_altitude focus directrix directrixNonNull
  have constantEqual :
      (parabolaAxis focus directrix).c =
        (altitudeThrough point directrix).c := by
    apply altitudeThrough_unique point directrix (parabolaAxis focus directrix)
    · rfl
    · rfl
    · exact onAxis
  have focusFootOnPointAltitude :
      (altitudeThrough point directrix).Contains focusFoot := by
    unfold Line.Contains at focusFootOnAxis ⊢
    change
      -directrix.b * focusFoot.x + directrix.a * focusFoot.y +
          (altitudeThrough point directrix).c = 0
    rw [← constantEqual]
    exact focusFootOnAxis
  exact (altitudeFoot_unique point directrix directrixNonNull focusFoot
    focusFootOnDirectrix focusFootOnPointAltitude).symm

/-- The vertex candidate lies on the canonical axis. -/
theorem parabolaVertex_on_axis
    (focus : Point K) (directrix : Line K)
    (directrixNonNull : ¬ directrix.IsNull)
    (twoNonzero : (2 : K) ≠ 0) :
    (parabolaAxis focus directrix).Contains
      (parabolaVertex focus directrix directrixNonNull) := by
  have focusContains := parabolaAxis_contains_focus focus directrix
  have footContains :
      (parabolaAxis focus directrix).Contains
        (altitudeFoot focus directrix directrixNonNull) :=
    altitudeFoot_on_altitude focus directrix directrixNonNull
  unfold Line.Contains at focusContains footContains ⊢
  unfold parabolaVertex midpoint
  have firstCoordinateCancel :
      (focus.x + (altitudeFoot focus directrix directrixNonNull).x) / 2 * 2 =
        focus.x + (altitudeFoot focus directrix directrixNonNull).x :=
    RFAP.ExplicitField.div_mul_cancel _ twoNonzero
  have secondCoordinateCancel :
      (focus.y + (altitudeFoot focus directrix directrixNonNull).y) / 2 * 2 =
        focus.y + (altitudeFoot focus directrix directrixNonNull).y :=
    RFAP.ExplicitField.div_mul_cancel _ twoNonzero
  apply eq_zero_of_mul_eq_zero_left twoNonzero
  calc
    2 *
        ((parabolaAxis focus directrix).a *
            ((focus.x +
              (altitudeFoot focus directrix directrixNonNull).x) / 2) +
          (parabolaAxis focus directrix).b *
            ((focus.y +
              (altitudeFoot focus directrix directrixNonNull).y) / 2) +
          (parabolaAxis focus directrix).c) =
      ((parabolaAxis focus directrix).a * focus.x +
          (parabolaAxis focus directrix).b * focus.y +
          (parabolaAxis focus directrix).c) +
        ((parabolaAxis focus directrix).a *
            (altitudeFoot focus directrix directrixNonNull).x +
          (parabolaAxis focus directrix).b *
            (altitudeFoot focus directrix directrixNonNull).y +
          (parabolaAxis focus directrix).c) := by
            calc
              2 *
                  ((parabolaAxis focus directrix).a *
                      ((focus.x +
                        (altitudeFoot focus directrix
                          directrixNonNull).x) / 2) +
                    (parabolaAxis focus directrix).b *
                      ((focus.y +
                        (altitudeFoot focus directrix
                          directrixNonNull).y) / 2) +
                    (parabolaAxis focus directrix).c) =
                (parabolaAxis focus directrix).a *
                    (((focus.x +
                      (altitudeFoot focus directrix
                        directrixNonNull).x) / 2) * 2) +
                  (parabolaAxis focus directrix).b *
                    (((focus.y +
                      (altitudeFoot focus directrix
                        directrixNonNull).y) / 2) * 2) +
                  2 * (parabolaAxis focus directrix).c := by ring1
              _ = _ := by
                rw [firstCoordinateCancel, secondCoordinateCancel]
                ring1
    _ = 0 := by rw [focusContains, footContains]; ring1

/-- The vertex candidate lies on the presented parabola. -/
theorem parabolaVertex_contains [DecidableEq K]
    (conic : Conic K) (focus : Point K) (directrix : Line K)
    (presentation : ParabolaPresentationData conic focus directrix)
    (twoNonzero : (2 : K) ≠ 0) :
    conic.Contains
      (parabolaVertex focus directrix presentation.directrixNonNull) := by
  let vertex :=
    parabolaVertex focus directrix presentation.directrixNonNull
  have vertexOnAxis : (parabolaAxis focus directrix).Contains vertex :=
    parabolaVertex_on_axis focus directrix presentation.directrixNonNull
      twoNonzero
  have vertexFoot :=
    altitudeFoot_eq_focusFoot_of_on_parabolaAxis focus vertex directrix
      presentation.directrixNonNull vertexOnAxis
  apply (contains_iff_equal_quadrances_of_presentation presentation).2
  unfold pointLineQuadrance
  rw [vertexFoot]
  exact midpoint_equal_quadrance focus
    (altitudeFoot focus directrix presentation.directrixNonNull) twoNonzero

/-- The focus-to-foot side is non-null; its quadrance is the nonzero
quadrance from the focus to the directrix. -/
theorem focus_directrixFoot_line_nonNull [DecidableEq K]
    {conic : Conic K} {focus : Point K} {directrix : Line K}
    (presentation : ParabolaPresentationData conic focus directrix) :
    let focusFoot :=
      altitudeFoot focus directrix presentation.directrixNonNull
    let distinct := focus_ne_directrixFoot presentation
    ¬ (lineThrough focus focusFoot distinct).IsNull := by
  dsimp only
  let focusFoot :=
    altitudeFoot focus directrix presentation.directrixNonNull
  have lineValueNonzero : lineValue directrix focus ≠ 0 := by
    intro valueZero
    apply presentation.focusNotOnDirectrix
    exact valueZero
  have valueSquareNonzero : lineValue directrix focus ^ 2 ≠ 0 := by
    simpa only [pow_two] using
      RFAP.ExplicitField.mul_ne_zero lineValueNonzero lineValueNonzero
  have focusLineQuadranceNonzero :
      pointLineQuadrance focus directrix presentation.directrixNonNull ≠ 0 := by
    rw [pointLineQuadrance_formula]
    exact RFAP.ExplicitField.div_ne_zero valueSquareNonzero
      presentation.directrixNonNull
  have focusFootQuadranceNonzero : quadrance focus focusFoot ≠ 0 := by
    exact focusLineQuadranceNonzero
  intro sideNull
  exact focusFootQuadranceNonzero
    ((null_line_iff_quadrance_zero focus focusFoot
      (focus_ne_directrixFoot presentation)).1 sideNull)

/-- Any point lying both on a presented parabola and its canonical axis is the
displayed vertex. -/
theorem parabolaVertex_unique [DecidableEq K]
    (conic : Conic K) (focus point : Point K) (directrix : Line K)
    (presentation : ParabolaPresentationData conic focus directrix)
    (twoNonzero : (2 : K) ≠ 0)
    (onParabola : conic.Contains point)
    (onAxis : (parabolaAxis focus directrix).Contains point) :
    point = parabolaVertex focus directrix presentation.directrixNonNull := by
  let focusFoot :=
    altitudeFoot focus directrix presentation.directrixNonNull
  have distinct : focus ≠ focusFoot := focus_ne_directrixFoot presentation
  have throughEquivalentAxis :
      (lineThrough focus focusFoot distinct).Equivalent
        (parabolaAxis focus directrix) := by
    apply lineThrough_unique focus focusFoot distinct
    · exact parabolaAxis_contains_focus focus directrix
    · exact altitudeFoot_on_altitude focus directrix
        presentation.directrixNonNull
  have pointOnThrough :
      (lineThrough focus focusFoot distinct).Contains point := by
    exact line_contains_of_equivalent
      (Line.equivalent_symm throughEquivalentAxis) point onAxis
  have pointFoot :=
    altitudeFoot_eq_focusFoot_of_on_parabolaAxis focus point directrix
      presentation.directrixNonNull onAxis
  have equalQuadrances :
      quadrance point focus = quadrance point focusFoot := by
    have metricEquality :=
      (contains_iff_equal_quadrances_of_presentation presentation).1
        onParabola
    calc
      quadrance point focus =
          pointLineQuadrance point directrix
            presentation.directrixNonNull := metricEquality
      _ = quadrance point
          (altitudeFoot point directrix presentation.directrixNonNull) := rfl
      _ = quadrance point focusFoot := by rw [pointFoot]
  have sideNonNull :
      ¬ (lineThrough focus focusFoot distinct).IsNull :=
    focus_directrixFoot_line_nonNull presentation
  have midpointUnique := midpoint_unique_of_equal_quadrance focus focusFoot
    point distinct twoNonzero sideNonNull pointOnThrough equalQuadrances
  exact midpointUnique

/-- Exercise 15.9: a presented parabola and its unique axis have exactly one
common point, the explicit focus/directrix midpoint vertex. -/
theorem exercise_15_9 [DecidableEq K]
    (conic : Conic K) (twoNonzero : (2 : K) ≠ 0)
    (isParabola : conic.IsParabola) :
    ∃ focus : Point K, ∃ directrix : Line K,
      ∃ presentation : ParabolaPresentationData conic focus directrix,
        let vertex := parabolaVertex focus directrix
          presentation.directrixNonNull
        conic.Contains vertex ∧
          (parabolaAxis focus directrix).Contains vertex ∧
          ∀ point : Point K, conic.Contains point →
            (parabolaAxis focus directrix).Contains point → point = vertex := by
  rcases isParabola with ⟨focus, directrix, presentation⟩
  rcases presentation with ⟨presentation⟩
  let vertex :=
    parabolaVertex focus directrix presentation.directrixNonNull
  refine ⟨focus, directrix, presentation, ?_, ?_, ?_⟩
  · exact parabolaVertex_contains conic focus directrix presentation
      twoNonzero
  · exact parabolaVertex_on_axis focus directrix
      presentation.directrixNonNull twoNonzero
  · intro point onParabola onAxis
    exact parabolaVertex_unique conic focus point directrix presentation
      twoNonzero onParabola onAxis





end Conic

end DivineProportions
