import mathlib.Tactic.QuotientFreeRing
import DivineProportions.Conics.Center
import DivineProportions.Trigonometry.Quadrance

/-!
# Divine Proportions, §15.2: circles

Circle presentations retain the arbitrary nonzero common scale of the source's
six-coefficient conic notation.  Thus Theorem 100 proves genuine recovery of a
center and quadrance from a displayed conic rather than storing them as data.
-/

namespace DivineProportions

variable {K : Type*} [RFAP.ExplicitField K]

namespace Conic

/-- A conic presents the equation `Q(X,C) = k`, up to the displayed nonzero
common coefficient `d`. -/
def IsCirclePresentation (conic : Conic K) (center : Point K)
    (circleQuadrance : K) : Prop :=
  conic.e = 0 ∧
    conic.d = conic.f ∧
    conic.d ≠ 0 ∧
    conic.a = -2 * conic.d * center.x ∧
    conic.b = -2 * conic.d * center.y ∧
    conic.c = conic.d *
      (center.x ^ 2 + center.y ^ 2 - circleQuadrance)

/-- A circle is a conic with an explicitly exhibited center and quadrance. -/
def IsCircle (conic : Conic K) : Prop :=
  ∃ center : Point K, ∃ circleQuadrance : K,
    conic.IsCirclePresentation center circleQuadrance

/-- The normalized coefficient record of `Q(X,C) = k`. -/
def circleConic [Nontrivial K] (center : Point K)
    (circleQuadrance : K) : Conic K where
  d := 1
  e := 0
  f := 1
  a := -2 * center.x
  b := -2 * center.y
  c := center.x ^ 2 + center.y ^ 2 - circleQuadrance
  quadratic_nonzero := Or.inl one_ne_zero

/-- The normalized construction has the claimed circle presentation. -/
theorem circleConic_isCirclePresentation [Nontrivial K] (center : Point K)
    (circleQuadrance : K) :
    (circleConic center circleQuadrance).IsCirclePresentation
      center circleQuadrance := by
  unfold circleConic IsCirclePresentation
  exact ⟨rfl, rfl, one_ne_zero, by ring1, by ring1, by ring1⟩

/-- Expanding a normalized circle gives `Q(X,C)-k`. -/
theorem circleConic_evaluate [Nontrivial K] (center point : Point K)
    (circleQuadrance : K) :
    (circleConic center circleQuadrance).evaluate point =
      quadrance point center - circleQuadrance := by
  unfold circleConic evaluate quadrance
  ring1

/-- Expanding any scaled circle presentation gives the same equation with a
visible nonzero scale. -/
theorem evaluate_eq_scale_mul_quadrance_sub
    (conic : Conic K) (center point : Point K) (circleQuadrance : K)
    (presentation : conic.IsCirclePresentation center circleQuadrance) :
    conic.evaluate point =
      conic.d * (quadrance point center - circleQuadrance) := by
  rcases presentation with
    ⟨eZero, dEqualsF, _, aFormula, bFormula, cFormula⟩
  unfold evaluate quadrance
  rw [eZero, ← dEqualsF, aFormula, bFormula, cFormula]
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

/-- A point lies on a presented circle exactly when its quadrance from the
displayed center has the displayed value. -/
theorem contains_iff_quadrance_eq
    (conic : Conic K) (center point : Point K) (circleQuadrance : K)
    (presentation : conic.IsCirclePresentation center circleQuadrance) :
    conic.Contains point ↔ quadrance point center = circleQuadrance := by
  have dNonzero := presentation.2.2.1
  rw [Contains, evaluate_eq_scale_mul_quadrance_sub conic center point
    circleQuadrance presentation]
  constructor
  · intro scaledZero
    have differenceZero :=
      eq_zero_of_mul_eq_zero_left dNonzero scaledZero
    calc
      quadrance point center =
          (quadrance point center - circleQuadrance) + circleQuadrance := by
            ring1
      _ = circleQuadrance := by rw [differenceZero]; ring1
  · intro equality
    rw [equality]
    ring1

private theorem negative_two_nonzero (twoNonzero : (2 : K) ≠ 0) :
    (-2 : K) ≠ 0 := by
  intro negativeTwoZero
  apply twoNonzero
  calc
    (2 : K) = -(-2) := by ring1
    _ = -0 := by rw [negativeTwoZero]
    _ = 0 := neg_zero

/-- Theorem 100 (Circle uniqueness): two circle equations presenting the same
displayed conic have the same center and the same quadrance. -/
theorem circle_uniqueness (conic : Conic K) (twoNonzero : (2 : K) ≠ 0)
    {center otherCenter : Point K} {circleQuadrance otherQuadrance : K}
    (presentation :
      conic.IsCirclePresentation center circleQuadrance)
    (otherPresentation :
      conic.IsCirclePresentation otherCenter otherQuadrance) :
    center = otherCenter ∧ circleQuadrance = otherQuadrance := by
  have dNonzero := presentation.2.2.1
  have scaleNonzero : -2 * conic.d ≠ 0 :=
    RFAP.ExplicitField.mul_ne_zero
      (negative_two_nonzero twoNonzero) dNonzero
  have xEqual : center.x = otherCenter.x := by
    apply eq_of_mul_eq_mul_left scaleNonzero
    calc
      (-2 * conic.d) * center.x = conic.a :=
        presentation.2.2.2.1.symm
      _ = (-2 * conic.d) * otherCenter.x :=
        otherPresentation.2.2.2.1
  have yEqual : center.y = otherCenter.y := by
    apply eq_of_mul_eq_mul_left scaleNonzero
    calc
      (-2 * conic.d) * center.y = conic.b :=
        presentation.2.2.2.2.1.symm
      _ = (-2 * conic.d) * otherCenter.y :=
        otherPresentation.2.2.2.2.1
  have centersEqual : center = otherCenter := Point.ext xEqual yEqual
  have scaledConstantsEqual :
      conic.d *
          (center.x ^ 2 + center.y ^ 2 - circleQuadrance) =
        conic.d *
          (center.x ^ 2 + center.y ^ 2 - otherQuadrance) := by
    calc
      conic.d *
          (center.x ^ 2 + center.y ^ 2 - circleQuadrance) = conic.c :=
        presentation.2.2.2.2.2.symm
      _ = conic.d *
          (otherCenter.x ^ 2 + otherCenter.y ^ 2 - otherQuadrance) :=
        otherPresentation.2.2.2.2.2
      _ = conic.d *
          (center.x ^ 2 + center.y ^ 2 - otherQuadrance) := by
        rw [← centersEqual]
  have constantsEqual :=
    eq_of_mul_eq_mul_left dNonzero scaledConstantsEqual
  have quadrancesEqual : circleQuadrance = otherQuadrance := by
    calc
      circleQuadrance =
          center.x ^ 2 + center.y ^ 2 -
            (center.x ^ 2 + center.y ^ 2 - circleQuadrance) := by ring1
      _ = center.x ^ 2 + center.y ^ 2 -
          (center.x ^ 2 + center.y ^ 2 - otherQuadrance) := by
        rw [constantsEqual]
      _ = otherQuadrance := by ring1
  exact ⟨centersEqual, quadrancesEqual⟩

/-- Theorem 100 packaged as unique existence from the definition of circle. -/
theorem circle_has_unique_presentation (conic : Conic K)
    (twoNonzero : (2 : K) ≠ 0) (isCircle : conic.IsCircle) :
    ∃ center : Point K, ∃ circleQuadrance : K,
      conic.IsCirclePresentation center circleQuadrance ∧
        ∀ otherCenter : Point K, ∀ otherQuadrance : K,
          conic.IsCirclePresentation otherCenter otherQuadrance →
            otherCenter = center ∧ otherQuadrance = circleQuadrance := by
  rcases isCircle with ⟨center, circleQuadrance, presentation⟩
  refine ⟨center, circleQuadrance, presentation, ?_⟩
  intro otherCenter otherQuadrance otherPresentation
  exact circle_uniqueness conic twoNonzero otherPresentation presentation

/-- Exercise 15.4: a conic is a circle exactly when `e=0` and its two square
coefficients are equal and nonzero.  The reverse direction constructs the
center and quadrance explicitly. -/
theorem exercise_15_4 (conic : Conic K) (twoNonzero : (2 : K) ≠ 0) :
    conic.IsCircle ↔
      conic.e = 0 ∧ conic.d = conic.f ∧ conic.d ≠ 0 := by
  constructor
  · rintro ⟨center, circleQuadrance, presentation⟩
    exact ⟨presentation.1, presentation.2.1, presentation.2.2.1⟩
  · rintro ⟨eZero, dEqualsF, dNonzero⟩
    have scaleNonzero : -2 * conic.d ≠ 0 :=
      RFAP.ExplicitField.mul_ne_zero
        (negative_two_nonzero twoNonzero) dNonzero
    let center : Point K :=
      ⟨conic.a / (-2 * conic.d), conic.b / (-2 * conic.d)⟩
    let circleQuadrance : K :=
      center.x ^ 2 + center.y ^ 2 - conic.c / conic.d
    refine ⟨center, circleQuadrance, eZero, dEqualsF, dNonzero, ?_, ?_, ?_⟩
    · dsimp only [center]
      calc
        conic.a =
            (conic.a / (-2 * conic.d)) * (-2 * conic.d) := by
          exact (RFAP.ExplicitField.div_mul_cancel conic.a scaleNonzero).symm
        _ = -2 * conic.d * (conic.a / (-2 * conic.d)) := by ring1
    · dsimp only [center]
      calc
        conic.b =
            (conic.b / (-2 * conic.d)) * (-2 * conic.d) := by
          exact (RFAP.ExplicitField.div_mul_cancel conic.b scaleNonzero).symm
        _ = -2 * conic.d * (conic.b / (-2 * conic.d)) := by ring1
    · dsimp only [circleQuadrance]
      calc
        conic.c = (conic.c / conic.d) * conic.d := by
          exact (RFAP.ExplicitField.div_mul_cancel conic.c dNonzero).symm
        _ = conic.d *
            (center.x ^ 2 + center.y ^ 2 -
              (center.x ^ 2 + center.y ^ 2 - conic.c / conic.d)) := by
                ring1

/-- The first line in Exercise 15.5. -/
def exercise15FiveFirstLine (twoNonzero : (2 : K) ≠ 0) : Line K where
  a := 2
  b := 3
  c := 0
  direction_nonzero := Or.inl twoNonzero

/-- The second line in Exercise 15.5. -/
def exercise15FiveSecondLine (threeNonzero : (3 : K) ≠ 0) : Line K where
  a := 3
  b := 2
  c := 0
  direction_nonzero := Or.inl threeNonzero

/-- Exercise 15.5, including its requested generalization: in any constructive
field of characteristic thirteen, the central null circle is exactly the union
of the two displayed null lines. -/
theorem exercise_15_5 [DecidableEq K] [Nontrivial K]
    (twoNonzero : (2 : K) ≠ 0) (threeNonzero : (3 : K) ≠ 0)
    (thirteenZero : (13 : K) = 0) (point : Point K) :
    (circleConic (⟨0, 0⟩ : Point K) 0).Contains point ↔
      (exercise15FiveFirstLine twoNonzero).Contains point ∨
        (exercise15FiveSecondLine threeNonzero).Contains point := by
  have sixNonzero : (6 : K) ≠ 0 := by
    have twoTimesThreeNonzero : (2 : K) * 3 ≠ 0 :=
      RFAP.ExplicitField.mul_ne_zero twoNonzero threeNonzero
    intro sixZero
    apply twoTimesThreeNonzero
    calc
      (2 : K) * 3 = 6 := by ring1
      _ = 0 := sixZero
  have factorization :
      ((2 : K) * point.x + 3 * point.y) *
          (3 * point.x + 2 * point.y) =
        6 * (point.x ^ 2 + point.y ^ 2) := by
    calc
      ((2 : K) * point.x + 3 * point.y) *
          (3 * point.x + 2 * point.y) =
        6 * (point.x ^ 2 + point.y ^ 2) +
          13 * point.x * point.y := by ring1
      _ = 6 * (point.x ^ 2 + point.y ^ 2) := by
        rw [thirteenZero]
        ring1
  simp only [Contains, circleConic, evaluate, exercise15FiveFirstLine,
    exercise15FiveSecondLine, Line.Contains, one_mul, zero_mul, add_zero,
    mul_zero, sub_zero, zero_pow (by decide : 2 ≠ 0)]
  change point.x ^ 2 + point.y ^ 2 = 0 ↔
    (2 : K) * point.x + 3 * point.y = 0 ∨
      3 * point.x + 2 * point.y = 0
  constructor
  · intro circleEquation
    have productZero :
        ((2 : K) * point.x + 3 * point.y) *
          (3 * point.x + 2 * point.y) = 0 := by
      rw [factorization, circleEquation]
      ring1
    by_cases firstFactorZero : (2 : K) * point.x + 3 * point.y = 0
    · exact Or.inl firstFactorZero
    · exact Or.inr
        (eq_zero_of_mul_eq_zero_left firstFactorZero productZero)
  · intro onLine
    have productZero :
        ((2 : K) * point.x + 3 * point.y) *
          (3 * point.x + 2 * point.y) = 0 := by
      rcases onLine with firstFactorZero | secondFactorZero
      · rw [firstFactorZero]
        ring1
      · rw [secondFactorZero]
        ring1
    apply eq_zero_of_mul_eq_zero_left sixNonzero
    calc
      6 * (point.x ^ 2 + point.y ^ 2) =
          ((2 : K) * point.x + 3 * point.y) *
            (3 * point.x + 2 * point.y) := factorization.symm
      _ = 0 := productZero

end Conic

end DivineProportions
