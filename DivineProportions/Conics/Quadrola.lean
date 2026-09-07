import DivineProportions.Conics.Axis
import DivineProportions.Conics.Tangent

/-!
# Divine Proportions, §15.4 and Exercise 19.3: quadrolas

A quadrola is given by one finite Archimedes polynomial in the two focal
quadrances and its associated quadrance.  The apparent quartic terms cancel
to an explicit conic.  Its gradient tangent satisfies the equal-spread
reflection property by a denominator-cleared polynomial identity.
-/

namespace DivineProportions

namespace Quadrola

variable {K : Type*} [RFAP.ExplicitField K]

/-- The defining equation (15.4). -/
def evaluate (firstFocus secondFocus : Point K)
    (associatedQuadrance : K) (point : Point K) : K :=
  archimedesFunction (quadrance point firstFocus)
    (quadrance point secondFocus) associatedQuadrance

def Contains (firstFocus secondFocus : Point K)
    (associatedQuadrance : K) (point : Point K) : Prop :=
  evaluate firstFocus secondFocus associatedQuadrance point = 0

/-- The nondegeneracy data required by the definition in §15.4. -/
structure Presentation (firstFocus secondFocus : Point K)
    (associatedQuadrance : K) : Prop where
  fociDistinct : firstFocus ≠ secondFocus
  associatedNonzero : associatedQuadrance ≠ 0
  focusQuadranceNonzero : quadrance firstFocus secondFocus ≠ 0
  focusQuadranceDifferent :
    quadrance firstFocus secondFocus ≠ associatedQuadrance

/-- The finite hypothesis in Exercise 15.10: no displayed field element has
square `-1`. -/
def NoSquareRootOfNegativeOne : Prop :=
  ∀ value : K, value ^ 2 ≠ -1

/-- The linear difference `Q(X,F₁)-Q(X,F₂)`. -/
def quadranceDifferenceLinear
    (firstFocus secondFocus : Point K) (point : Point K) : K :=
  2 * (secondFocus.x - firstFocus.x) * point.x +
    2 * (secondFocus.y - firstFocus.y) * point.y +
    firstFocus.x ^ 2 + firstFocus.y ^ 2 -
    secondFocus.x ^ 2 - secondFocus.y ^ 2

/-- Difference of the two focal quadrances is exactly linear in the point. -/
theorem quadrance_difference
    (firstFocus secondFocus point : Point K) :
    quadrance point firstFocus - quadrance point secondFocus =
      quadranceDifferenceLinear firstFocus secondFocus point := by
  unfold quadrance quadranceDifferenceLinear
  ring1

/-- The Archimedes polynomial in a form where quartic cancellation is
visible. -/
theorem archimedes_difference_identity (first second third : K) :
    archimedesFunction first second third =
      -(first - second) ^ 2 + 2 * third * (first + second) - third ^ 2 := by
  unfold archimedesFunction
  ring1

/-- The `x²` coefficient after expansion of the quadrola equation. -/
def conicD (firstFocus secondFocus : Point K)
    (associatedQuadrance : K) : K :=
  4 * (associatedQuadrance - (secondFocus.x - firstFocus.x) ^ 2)

/-- The `xy` coefficient after expansion. -/
def conicE (firstFocus secondFocus : Point K) : K :=
  -8 * (secondFocus.x - firstFocus.x) *
    (secondFocus.y - firstFocus.y)

/-- The `y²` coefficient after expansion. -/
def conicF (firstFocus secondFocus : Point K)
    (associatedQuadrance : K) : K :=
  4 * (associatedQuadrance - (secondFocus.y - firstFocus.y) ^ 2)

def conicA (firstFocus secondFocus : Point K)
    (associatedQuadrance : K) : K :=
  -4 * ((secondFocus.x - firstFocus.x) *
      (firstFocus.x ^ 2 + firstFocus.y ^ 2 -
        secondFocus.x ^ 2 - secondFocus.y ^ 2) +
    associatedQuadrance * (firstFocus.x + secondFocus.x))

def conicB (firstFocus secondFocus : Point K)
    (associatedQuadrance : K) : K :=
  -4 * ((secondFocus.y - firstFocus.y) *
      (firstFocus.x ^ 2 + firstFocus.y ^ 2 -
        secondFocus.x ^ 2 - secondFocus.y ^ 2) +
    associatedQuadrance * (firstFocus.y + secondFocus.y))

def conicC (firstFocus secondFocus : Point K)
    (associatedQuadrance : K) : K :=
  -(firstFocus.x ^ 2 + firstFocus.y ^ 2 -
      secondFocus.x ^ 2 - secondFocus.y ^ 2) ^ 2 +
    2 * associatedQuadrance *
      (firstFocus.x ^ 2 + firstFocus.y ^ 2 +
        secondFocus.x ^ 2 + secondFocus.y ^ 2) -
    associatedQuadrance ^ 2

private theorem four_nonzero_of_eight_nonzero
    (eightNonzero : (8 : K) ≠ 0) : (4 : K) ≠ 0 := by
  intro fourZero
  apply eightNonzero
  calc
    (8 : K) = 2 * 4 := by ring1
    _ = 0 := by rw [fourZero]; ring1

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

private theorem eq_or_eq_neg_of_square_eq [DecidableEq K]
    {left right : K} (squaresEqual : left ^ 2 = right ^ 2) :
    left = right ∨ left = -right := by
  by_cases equal : left = right
  · exact Or.inl equal
  · right
    have differenceNonzero : left - right ≠ 0 := by
      intro differenceZero
      apply equal
      calc
        left = (left - right) + right := by ring1
        _ = right := by rw [differenceZero]; ring1
    have productZero : (left - right) * (left + right) = 0 := by
      calc
        (left - right) * (left + right) = left ^ 2 - right ^ 2 := by
          ring1
        _ = 0 := by rw [squaresEqual]; ring1
    have sumZero :=
      eq_zero_of_nonzero_mul_left differenceNonzero productZero
    calc
      left = (left + right) - right := by ring1
      _ = -right := by rw [sumZero]; ring1

/-- Algebraic core of Exercise 15.10.  Two focal-difference vectors giving
the same three normalized quadratic coefficients are equal up to sign when
`-1` has no square root; their associated quadrances are then equal. -/
theorem parameters_unique_of_quadratic_coefficients [DecidableEq K]
    (firstX firstY secondX secondY : K)
    (firstAssociated secondAssociated : K)
    (noNegativeOneSquare : NoSquareRootOfNegativeOne (K := K))
    (dEqual :
      firstAssociated - firstX ^ 2 =
        secondAssociated - secondX ^ 2)
    (mixedEqual : firstX * firstY = secondX * secondY)
    (fEqual :
      firstAssociated - firstY ^ 2 =
        secondAssociated - secondY ^ 2) :
    firstAssociated = secondAssociated ∧
      ((firstX = secondX ∧ firstY = secondY) ∨
        (firstX = -secondX ∧ firstY = -secondY)) := by
  have firstDifference :
      firstAssociated - secondAssociated = firstX ^ 2 - secondX ^ 2 := by
    calc
      firstAssociated - secondAssociated =
          (firstAssociated - firstX ^ 2) -
            (secondAssociated - secondX ^ 2) +
            (firstX ^ 2 - secondX ^ 2) := by ring1
      _ = firstX ^ 2 - secondX ^ 2 := by rw [dEqual]; ring1
  have secondDifference :
      firstAssociated - secondAssociated = firstY ^ 2 - secondY ^ 2 := by
    calc
      firstAssociated - secondAssociated =
          (firstAssociated - firstY ^ 2) -
            (secondAssociated - secondY ^ 2) +
            (firstY ^ 2 - secondY ^ 2) := by ring1
      _ = firstY ^ 2 - secondY ^ 2 := by rw [fEqual]; ring1
  have differenceProduct :
      (firstAssociated - secondAssociated) ^ 2 =
        (firstX ^ 2 - secondX ^ 2) *
          (firstY ^ 2 - secondY ^ 2) := by
    rw [← firstDifference, ← secondDifference]
    ring1
  let cross := firstX * secondY - firstY * secondX
  have negativeSquareIdentity :
      (firstAssociated - secondAssociated) ^ 2 + cross ^ 2 = 0 := by
    calc
      (firstAssociated - secondAssociated) ^ 2 + cross ^ 2 =
          (firstX ^ 2 - secondX ^ 2) *
              (firstY ^ 2 - secondY ^ 2) + cross ^ 2 := by
        rw [differenceProduct]
      _ = (firstX * firstY - secondX * secondY) ^ 2 := by
        unfold cross
        ring1
      _ = 0 := by rw [mixedEqual]; ring1
  have associatedDifferenceZero :
      firstAssociated - secondAssociated = 0 := by
    by_cases differenceZero : firstAssociated - secondAssociated = 0
    · exact differenceZero
    · have differenceCancel :
          (firstAssociated - secondAssociated) *
              (firstAssociated - secondAssociated)⁻¹ = (1 : K) :=
        RFAP.ExplicitField.mul_inv_cancel _ differenceZero
      have candidateSquare :
          (cross / (firstAssociated - secondAssociated)) ^ 2 = -1 := by
        simp only [RFAP.ExplicitField.div_eq_mul_inv]
        calc
          (cross * (firstAssociated - secondAssociated)⁻¹) ^ 2 =
              cross ^ 2 *
                (firstAssociated - secondAssociated)⁻¹ ^ 2 := by ring1
          _ = -(firstAssociated - secondAssociated) ^ 2 *
                (firstAssociated - secondAssociated)⁻¹ ^ 2 := by
            have crossSquare :
                cross ^ 2 = -(firstAssociated - secondAssociated) ^ 2 := by
              calc
                cross ^ 2 =
                    ((firstAssociated - secondAssociated) ^ 2 + cross ^ 2) -
                      (firstAssociated - secondAssociated) ^ 2 := by ring1
                _ = -(firstAssociated - secondAssociated) ^ 2 := by
                  rw [negativeSquareIdentity]
                  ring1
            rw [crossSquare]
          _ = -((firstAssociated - secondAssociated) *
                (firstAssociated - secondAssociated)⁻¹) ^ 2 := by ring1
          _ = -1 := by rw [differenceCancel]; ring1
      exact False.elim
        ((noNegativeOneSquare
          (cross / (firstAssociated - secondAssociated))) candidateSquare)
  have associatedEqual : firstAssociated = secondAssociated := by
    calc
      firstAssociated =
          (firstAssociated - secondAssociated) + secondAssociated := by ring1
      _ = secondAssociated := by rw [associatedDifferenceZero]; ring1
  have firstSquaresEqual : firstX ^ 2 = secondX ^ 2 := by
    have squareDifferenceZero : firstX ^ 2 - secondX ^ 2 = 0 := by
      calc
        firstX ^ 2 - secondX ^ 2 =
            firstAssociated - secondAssociated := firstDifference.symm
        _ = 0 := associatedDifferenceZero
    calc
      firstX ^ 2 = (firstX ^ 2 - secondX ^ 2) + secondX ^ 2 := by ring1
      _ = secondX ^ 2 := by rw [squareDifferenceZero]; ring1
  have secondSquaresEqual : firstY ^ 2 = secondY ^ 2 := by
    have squareDifferenceZero : firstY ^ 2 - secondY ^ 2 = 0 := by
      calc
        firstY ^ 2 - secondY ^ 2 =
            firstAssociated - secondAssociated := secondDifference.symm
        _ = 0 := associatedDifferenceZero
    calc
      firstY ^ 2 = (firstY ^ 2 - secondY ^ 2) + secondY ^ 2 := by ring1
      _ = secondY ^ 2 := by rw [squareDifferenceZero]; ring1
  refine ⟨associatedEqual, ?_⟩
  by_cases firstXZero : firstX = 0
  · have secondXSquareZero : secondX ^ 2 = 0 := by
      rw [← firstSquaresEqual, firstXZero]
      ring1
    have secondXZero : secondX = 0 := by
      by_cases secondXZero : secondX = 0
      · exact secondXZero
      · exact False.elim
          ((RFAP.ExplicitField.mul_ne_zero secondXZero secondXZero)
            (by simpa only [pow_two] using secondXSquareZero))
    rcases eq_or_eq_neg_of_square_eq secondSquaresEqual with
      secondYEqual | secondYNegative
    · left
      exact ⟨by rw [firstXZero, secondXZero], secondYEqual⟩
    · right
      exact ⟨by rw [firstXZero, secondXZero]; ring1, secondYNegative⟩
  · rcases eq_or_eq_neg_of_square_eq firstSquaresEqual with
      firstXEqual | firstXNegative
    · left
      refine ⟨firstXEqual, ?_⟩
      have productZero : firstX * (firstY - secondY) = 0 := by
        calc
          firstX * (firstY - secondY) =
              firstX * firstY - secondX * secondY := by
            rw [← firstXEqual]
            ring1
          _ = 0 := by rw [mixedEqual]; ring1
      have differenceZero :=
        eq_zero_of_nonzero_mul_left firstXZero productZero
      calc
        firstY = (firstY - secondY) + secondY := by ring1
        _ = secondY := by rw [differenceZero]; ring1
    · right
      refine ⟨firstXNegative, ?_⟩
      have secondXEqualsNegative : secondX = -firstX := by
        calc
          secondX = -(-secondX) := by ring1
          _ = -firstX := by rw [firstXNegative]
      have productZero : firstX * (firstY + secondY) = 0 := by
        calc
          firstX * (firstY + secondY) =
              firstX * firstY - secondX * secondY := by
            rw [secondXEqualsNegative]
            ring1
          _ = 0 := by rw [mixedEqual]; ring1
      have sumZero := eq_zero_of_nonzero_mul_left firstXZero productZero
      calc
        firstY = (firstY + secondY) - secondY := by ring1
        _ = -secondY := by rw [sumZero]; ring1

private theorem conic_quadratic_nonzero [DecidableEq K]
    (firstFocus secondFocus : Point K) (associatedQuadrance : K)
    (associatedNonzero : associatedQuadrance ≠ 0)
    (eightNonzero : (8 : K) ≠ 0) :
    conicD firstFocus secondFocus associatedQuadrance ≠ 0 ∨
      conicE firstFocus secondFocus ≠ 0 ∨
      conicF firstFocus secondFocus associatedQuadrance ≠ 0 := by
  by_cases dZero : conicD firstFocus secondFocus associatedQuadrance = 0
  · by_cases eZero : conicE firstFocus secondFocus = 0
    · right
      right
      intro fZero
      let deltaX := secondFocus.x - firstFocus.x
      let deltaY := secondFocus.y - firstFocus.y
      have fourNonzero := four_nonzero_of_eight_nonzero eightNonzero
      have firstDifferenceZero :
          associatedQuadrance - deltaX ^ 2 = 0 := by
        apply eq_zero_of_nonzero_mul_left fourNonzero
        simpa only [conicD, deltaX] using dZero
      have secondDifferenceZero :
          associatedQuadrance - deltaY ^ 2 = 0 := by
        apply eq_zero_of_nonzero_mul_left fourNonzero
        simpa only [conicF, deltaY] using fZero
      have deltaProductZero : deltaX * deltaY = 0 := by
        apply eq_zero_of_nonzero_mul_left eightNonzero
        calc
          (8 : K) * (deltaX * deltaY) =
              -(conicE firstFocus secondFocus) := by
            unfold conicE deltaX deltaY
            ring1
          _ = 0 := by rw [eZero]; ring1
      have deltaXNonzero : deltaX ≠ 0 := by
        intro deltaXZero
        apply associatedNonzero
        calc
          associatedQuadrance =
              (associatedQuadrance - deltaX ^ 2) + deltaX ^ 2 := by ring1
          _ = 0 := by rw [firstDifferenceZero, deltaXZero]; ring1
      have deltaYZero :=
        eq_zero_of_nonzero_mul_left deltaXNonzero deltaProductZero
      apply associatedNonzero
      calc
        associatedQuadrance =
            (associatedQuadrance - deltaY ^ 2) + deltaY ^ 2 := by ring1
        _ = 0 := by rw [secondDifferenceZero, deltaYZero]; ring1
    · exact Or.inr (Or.inl eZero)
  · exact Or.inl dZero

/-- Exercise 15.11's explicit conic obtained from the quadrola equation. -/
def conic [DecidableEq K]
    (firstFocus secondFocus : Point K) (associatedQuadrance : K)
    (associatedNonzero : associatedQuadrance ≠ 0)
    (eightNonzero : (8 : K) ≠ 0) : Conic K where
  d := conicD firstFocus secondFocus associatedQuadrance
  e := conicE firstFocus secondFocus
  f := conicF firstFocus secondFocus associatedQuadrance
  a := conicA firstFocus secondFocus associatedQuadrance
  b := conicB firstFocus secondFocus associatedQuadrance
  c := conicC firstFocus secondFocus associatedQuadrance
  quadratic_nonzero := conic_quadratic_nonzero firstFocus secondFocus
    associatedQuadrance associatedNonzero eightNonzero

/-- Exercise 15.11: the six-coefficient conic evaluates to the defining
Archimedes polynomial. -/
theorem conic_evaluate [DecidableEq K]
    (firstFocus secondFocus : Point K) (associatedQuadrance : K)
    (associatedNonzero : associatedQuadrance ≠ 0)
    (eightNonzero : (8 : K) ≠ 0) (point : Point K) :
    (conic firstFocus secondFocus associatedQuadrance associatedNonzero
      eightNonzero).evaluate point =
        evaluate firstFocus secondFocus associatedQuadrance point := by
  unfold conic Conic.evaluate evaluate conicD conicE conicF conicA conicB
    conicC quadrance archimedesFunction
  ring1

/-- An explicit quotient-free witness that two displayed conic coefficient
records represent the same six-proportion. -/
structure CoefficientScale (source target : Conic K) (scale : K) : Prop where
  d : source.d = scale * target.d
  e : source.e = scale * target.e
  f : source.f = scale * target.f
  a : source.a = scale * target.a
  b : source.b = scale * target.b
  c : source.c = scale * target.c

theorem CoefficientScale.evaluate
    {source target : Conic K} {scale : K}
    (scaled : CoefficientScale source target scale) (point : Point K) :
    source.evaluate point = scale * target.evaluate point := by
  unfold Conic.evaluate
  rw [scaled.d, scaled.e, scaled.f, scaled.a, scaled.b, scaled.c]
  ring1

theorem CoefficientScale.discriminant
    {source target : Conic K} {scale : K}
    (scaled : CoefficientScale source target scale) :
    source.centerDiscriminant = scale ^ 2 * target.centerDiscriminant := by
  unfold Conic.centerDiscriminant
  rw [scaled.d, scaled.e, scaled.f]
  ring1

theorem CoefficientScale.isCenter
    {source target : Conic K} {scale : K}
    (scaled : CoefficientScale source target scale) (center : Point K)
    (targetCenter : target.IsCenter center) :
    source.IsCenter center := by
  rcases targetCenter with ⟨firstEquation, secondEquation⟩
  constructor
  · rw [scaled.d, scaled.e, scaled.a]
    calc
      2 * (scale * target.d) * center.x +
          scale * target.e * center.y + scale * target.a =
        scale * (2 * target.d * center.x + target.e * center.y +
          target.a) := by ring1
      _ = 0 := by rw [firstEquation]; ring1
  · rw [scaled.e, scaled.f, scaled.b]
    calc
      scale * target.e * center.x +
          2 * (scale * target.f) * center.y + scale * target.b =
        scale * (target.e * center.x + 2 * target.f * center.y +
          target.b) := by ring1
      _ = 0 := by rw [secondEquation]; ring1

/-- The center discriminant of the canonical quadrola coefficients. -/
theorem conic_centerDiscriminant [DecidableEq K]
    (firstFocus secondFocus : Point K) (associatedQuadrance : K)
    (associatedNonzero : associatedQuadrance ≠ 0)
    (eightNonzero : (8 : K) ≠ 0) :
    (conic firstFocus secondFocus associatedQuadrance associatedNonzero
      eightNonzero).centerDiscriminant =
        64 * associatedQuadrance *
          (quadrance firstFocus secondFocus - associatedQuadrance) := by
  unfold Conic.centerDiscriminant conic conicD conicE conicF quadrance
  ring1

/-- The canonical equation evaluated at the midpoint of its foci. -/
theorem conic_evaluate_midpoint [DecidableEq K]
    (firstFocus secondFocus : Point K) (associatedQuadrance : K)
    (associatedNonzero : associatedQuadrance ≠ 0)
    (eightNonzero : (8 : K) ≠ 0) (twoNonzero : (2 : K) ≠ 0) :
    (conic firstFocus secondFocus associatedQuadrance associatedNonzero
      eightNonzero).evaluate (midpoint firstFocus secondFocus) =
        associatedQuadrance *
          (quadrance firstFocus secondFocus - associatedQuadrance) := by
  have equalMidpointQuadrances :=
    midpoint_equal_quadrance firstFocus secondFocus twoNonzero
  have midpointValue := midpoint_quadrance firstFocus secondFocus twoNonzero
  have fourNonzero : (4 : K) ≠ 0 := by
    have fourAsProduct : (4 : K) = 2 * 2 := by ring1
    rw [fourAsProduct]
    exact RFAP.ExplicitField.mul_ne_zero twoNonzero twoNonzero
  have fourCancel : (4 : K) * (4 : K)⁻¹ = 1 :=
    RFAP.ExplicitField.mul_inv_cancel 4 fourNonzero
  calc
    (conic firstFocus secondFocus associatedQuadrance associatedNonzero
        eightNonzero).evaluate (midpoint firstFocus secondFocus) =
      evaluate firstFocus secondFocus associatedQuadrance
        (midpoint firstFocus secondFocus) :=
      conic_evaluate firstFocus secondFocus associatedQuadrance associatedNonzero
        eightNonzero (midpoint firstFocus secondFocus)
    _ = -(quadrance (midpoint firstFocus secondFocus) firstFocus -
            quadrance (midpoint firstFocus secondFocus) secondFocus) ^ 2 +
          2 * associatedQuadrance *
            (quadrance (midpoint firstFocus secondFocus) firstFocus +
              quadrance (midpoint firstFocus secondFocus) secondFocus) -
          associatedQuadrance ^ 2 := by
      unfold evaluate
      rw [archimedes_difference_identity]
    _ = 4 * associatedQuadrance *
          quadrance (midpoint firstFocus secondFocus) firstFocus -
          associatedQuadrance ^ 2 := by
      rw [equalMidpointQuadrances]
      ring1
    _ = 4 * associatedQuadrance *
          (quadrance firstFocus secondFocus * (4 : K)⁻¹) -
          associatedQuadrance ^ 2 := by
      rw [midpointValue, RFAP.ExplicitField.div_eq_mul_inv]
    _ = associatedQuadrance *
          (quadrance firstFocus secondFocus - associatedQuadrance) := by
      calc
        4 * associatedQuadrance *
              (quadrance firstFocus secondFocus * (4 : K)⁻¹) -
              associatedQuadrance ^ 2 =
            associatedQuadrance * quadrance firstFocus secondFocus *
                (4 * (4 : K)⁻¹) - associatedQuadrance ^ 2 := by ring1
        _ = associatedQuadrance *
            (quadrance firstFocus secondFocus - associatedQuadrance) := by
          rw [fourCancel]
          ring1

theorem conic_discriminant_nonzero [DecidableEq K]
    (firstFocus secondFocus : Point K) (associatedQuadrance : K)
    (presentation : Presentation firstFocus secondFocus associatedQuadrance)
    (eightNonzero : (8 : K) ≠ 0) :
    (conic firstFocus secondFocus associatedQuadrance
      presentation.associatedNonzero eightNonzero).centerDiscriminant ≠ 0 := by
  have sixtyFourNonzero : (64 : K) ≠ 0 := by
    have sixtyFourAsProduct : (64 : K) = 8 * 8 := by ring1
    rw [sixtyFourAsProduct]
    exact RFAP.ExplicitField.mul_ne_zero eightNonzero eightNonzero
  have differenceNonzero :
      quadrance firstFocus secondFocus - associatedQuadrance ≠ 0 := by
    intro differenceZero
    apply presentation.focusQuadranceDifferent
    calc
      quadrance firstFocus secondFocus =
          (quadrance firstFocus secondFocus - associatedQuadrance) +
            associatedQuadrance := by ring1
      _ = associatedQuadrance := by rw [differenceZero]; ring1
  rw [conic_centerDiscriminant]
  exact RFAP.ExplicitField.mul_ne_zero
    (RFAP.ExplicitField.mul_ne_zero sixtyFourNonzero
      presentation.associatedNonzero) differenceNonzero

private theorem conic_midpoint_isCenter [DecidableEq K]
    (firstFocus secondFocus : Point K) (associatedQuadrance : K)
    (associatedNonzero : associatedQuadrance ≠ 0)
    (eightNonzero : (8 : K) ≠ 0) (twoNonzero : (2 : K) ≠ 0) :
    (conic firstFocus secondFocus associatedQuadrance associatedNonzero
      eightNonzero).IsCenter (midpoint firstFocus secondFocus) := by
  have twoCancel : (2 : K) * (2 : K)⁻¹ = 1 :=
    RFAP.ExplicitField.mul_inv_cancel 2 twoNonzero
  have midpointX :
      2 * (midpoint firstFocus secondFocus).x =
        firstFocus.x + secondFocus.x := by
    change 2 * ((firstFocus.x + secondFocus.x) / 2) =
      firstFocus.x + secondFocus.x
    simp only [RFAP.ExplicitField.div_eq_mul_inv]
    calc
      2 * ((firstFocus.x + secondFocus.x) * (2 : K)⁻¹) =
          (firstFocus.x + secondFocus.x) * (2 * (2 : K)⁻¹) := by
            ring1
      _ = firstFocus.x + secondFocus.x := by rw [twoCancel]; ring1
  have midpointY :
      2 * (midpoint firstFocus secondFocus).y =
        firstFocus.y + secondFocus.y := by
    change 2 * ((firstFocus.y + secondFocus.y) / 2) =
      firstFocus.y + secondFocus.y
    simp only [RFAP.ExplicitField.div_eq_mul_inv]
    calc
      2 * ((firstFocus.y + secondFocus.y) * (2 : K)⁻¹) =
          (firstFocus.y + secondFocus.y) * (2 * (2 : K)⁻¹) := by
            ring1
      _ = firstFocus.y + secondFocus.y := by rw [twoCancel]; ring1
  constructor
  · change
      2 * conicD firstFocus secondFocus associatedQuadrance *
            (midpoint firstFocus secondFocus).x +
          conicE firstFocus secondFocus *
            (midpoint firstFocus secondFocus).y +
          conicA firstFocus secondFocus associatedQuadrance = 0
    calc
      2 * conicD firstFocus secondFocus associatedQuadrance *
              (midpoint firstFocus secondFocus).x +
            conicE firstFocus secondFocus *
              (midpoint firstFocus secondFocus).y +
            conicA firstFocus secondFocus associatedQuadrance =
          conicD firstFocus secondFocus associatedQuadrance *
              (2 * (midpoint firstFocus secondFocus).x) -
            4 * (secondFocus.x - firstFocus.x) *
                (secondFocus.y - firstFocus.y) *
              (2 * (midpoint firstFocus secondFocus).y) +
            conicA firstFocus secondFocus associatedQuadrance := by
              unfold conicE
              ring1
      _ = conicD firstFocus secondFocus associatedQuadrance *
              (firstFocus.x + secondFocus.x) -
            4 * (secondFocus.x - firstFocus.x) *
                (secondFocus.y - firstFocus.y) *
              (firstFocus.y + secondFocus.y) +
            conicA firstFocus secondFocus associatedQuadrance := by
              rw [midpointX, midpointY]
      _ = 0 := by unfold conicD conicA; ring1
  · change
      conicE firstFocus secondFocus *
            (midpoint firstFocus secondFocus).x +
          2 * conicF firstFocus secondFocus associatedQuadrance *
            (midpoint firstFocus secondFocus).y +
          conicB firstFocus secondFocus associatedQuadrance = 0
    calc
      conicE firstFocus secondFocus *
              (midpoint firstFocus secondFocus).x +
            2 * conicF firstFocus secondFocus associatedQuadrance *
              (midpoint firstFocus secondFocus).y +
            conicB firstFocus secondFocus associatedQuadrance =
          -4 * (secondFocus.x - firstFocus.x) *
                (secondFocus.y - firstFocus.y) *
              (2 * (midpoint firstFocus secondFocus).x) +
            conicF firstFocus secondFocus associatedQuadrance *
              (2 * (midpoint firstFocus secondFocus).y) +
            conicB firstFocus secondFocus associatedQuadrance := by
              unfold conicE
              ring1
      _ = -4 * (secondFocus.x - firstFocus.x) *
                (secondFocus.y - firstFocus.y) *
              (firstFocus.x + secondFocus.x) +
            conicF firstFocus secondFocus associatedQuadrance *
              (firstFocus.y + secondFocus.y) +
            conicB firstFocus secondFocus associatedQuadrance := by
              rw [midpointX, midpointY]
      _ = 0 := by unfold conicF conicB; ring1

private theorem endpoint_pairs_of_midpoint_and_difference
    (firstOne firstTwo secondOne secondTwo : Point K)
    (twoNonzero : (2 : K) ≠ 0)
    (midpointsEqual : midpoint firstOne firstTwo = midpoint secondOne secondTwo)
    (differences :
      ((firstTwo.x - firstOne.x = secondTwo.x - secondOne.x ∧
          firstTwo.y - firstOne.y = secondTwo.y - secondOne.y) ∨
        (firstTwo.x - firstOne.x = -(secondTwo.x - secondOne.x) ∧
          firstTwo.y - firstOne.y = -(secondTwo.y - secondOne.y)))) :
    (firstOne = secondOne ∧ firstTwo = secondTwo) ∨
      (firstOne = secondTwo ∧ firstTwo = secondOne) := by
  have twoCancel : (2 : K) * (2 : K)⁻¹ = 1 :=
    RFAP.ExplicitField.mul_inv_cancel 2 twoNonzero
  have sumX : firstOne.x + firstTwo.x = secondOne.x + secondTwo.x := by
    have midpointX := congrArg Point.x midpointsEqual
    have scaled := congrArg (fun value : K => 2 * value) midpointX
    calc
      firstOne.x + firstTwo.x =
          2 * ((firstOne.x + firstTwo.x) / 2) := by
        simp only [RFAP.ExplicitField.div_eq_mul_inv]
        calc
          firstOne.x + firstTwo.x =
              (firstOne.x + firstTwo.x) * (2 * (2 : K)⁻¹) := by
            rw [twoCancel]
            ring1
          _ = 2 * ((firstOne.x + firstTwo.x) * (2 : K)⁻¹) := by ring1
      _ = 2 * ((secondOne.x + secondTwo.x) / 2) := scaled
      _ = secondOne.x + secondTwo.x := by
        simp only [RFAP.ExplicitField.div_eq_mul_inv]
        calc
          2 * ((secondOne.x + secondTwo.x) * (2 : K)⁻¹) =
              (secondOne.x + secondTwo.x) * (2 * (2 : K)⁻¹) := by ring1
          _ = secondOne.x + secondTwo.x := by rw [twoCancel]; ring1
  have sumY : firstOne.y + firstTwo.y = secondOne.y + secondTwo.y := by
    have midpointY := congrArg Point.y midpointsEqual
    have scaled := congrArg (fun value : K => 2 * value) midpointY
    calc
      firstOne.y + firstTwo.y =
          2 * ((firstOne.y + firstTwo.y) / 2) := by
        simp only [RFAP.ExplicitField.div_eq_mul_inv]
        calc
          firstOne.y + firstTwo.y =
              (firstOne.y + firstTwo.y) * (2 * (2 : K)⁻¹) := by
            rw [twoCancel]
            ring1
          _ = 2 * ((firstOne.y + firstTwo.y) * (2 : K)⁻¹) := by ring1
      _ = 2 * ((secondOne.y + secondTwo.y) / 2) := scaled
      _ = secondOne.y + secondTwo.y := by
        simp only [RFAP.ExplicitField.div_eq_mul_inv]
        calc
          2 * ((secondOne.y + secondTwo.y) * (2 : K)⁻¹) =
              (secondOne.y + secondTwo.y) * (2 * (2 : K)⁻¹) := by ring1
          _ = secondOne.y + secondTwo.y := by rw [twoCancel]; ring1
  have orderedCoordinate :
      ∀ (firstLeft firstRight secondLeft secondRight : K),
        firstLeft + firstRight = secondLeft + secondRight →
        firstRight - firstLeft = secondRight - secondLeft →
        firstLeft = secondLeft ∧ firstRight = secondRight := by
    intro firstLeft firstRight secondLeft secondRight sumEqual differenceEqual
    have twiceLeftDifference :
        (2 : K) * (firstLeft - secondLeft) = 0 := by
      calc
        (2 : K) * (firstLeft - secondLeft) =
            (firstLeft + firstRight - (firstRight - firstLeft)) -
              (secondLeft + secondRight - (secondRight - secondLeft)) := by
          ring1
        _ = 0 := by rw [sumEqual, differenceEqual]; ring1
    have leftDifferenceZero :=
      eq_zero_of_nonzero_mul_left twoNonzero twiceLeftDifference
    have leftEqual : firstLeft = secondLeft := by
      calc
        firstLeft = (firstLeft - secondLeft) + secondLeft := by ring1
        _ = secondLeft := by rw [leftDifferenceZero]; ring1
    have rightEqual : firstRight = secondRight := by
      calc
        firstRight = (firstLeft + firstRight) - firstLeft := by ring1
        _ = (secondLeft + secondRight) - secondLeft := by
          rw [sumEqual, leftEqual]
        _ = secondRight := by ring1
    exact ⟨leftEqual, rightEqual⟩
  rcases differences with ordered | reversed
  · have xCoordinates := orderedCoordinate firstOne.x firstTwo.x
      secondOne.x secondTwo.x sumX ordered.1
    have yCoordinates := orderedCoordinate firstOne.y firstTwo.y
      secondOne.y secondTwo.y sumY ordered.2
    left
    exact ⟨Point.ext xCoordinates.1 yCoordinates.1,
      Point.ext xCoordinates.2 yCoordinates.2⟩
  · have reversedX :
        firstTwo.x - firstOne.x = secondOne.x - secondTwo.x := by
      calc
        firstTwo.x - firstOne.x =
            -(secondTwo.x - secondOne.x) := reversed.1
        _ = secondOne.x - secondTwo.x := by ring1
    have reversedY :
        firstTwo.y - firstOne.y = secondOne.y - secondTwo.y := by
      calc
        firstTwo.y - firstOne.y =
            -(secondTwo.y - secondOne.y) := reversed.2
        _ = secondOne.y - secondTwo.y := by ring1
    have xCoordinates := orderedCoordinate firstOne.x firstTwo.x
      secondTwo.x secondOne.x (by rw [sumX]; ring1) reversedX
    have yCoordinates := orderedCoordinate firstOne.y firstTwo.y
      secondTwo.y secondOne.y (by rw [sumY]; ring1) reversedY
    right
    exact ⟨Point.ext xCoordinates.1 yCoordinates.1,
      Point.ext xCoordinates.2 yCoordinates.2⟩

/-- Exercise 15.10 (Quadrola uniqueness).  When `-1` has no square root, two
valid focal presentations of the same displayed conic proportion have the
same associated quadrance and the same unordered pair of foci.  Equality of
conic proportions is carried by the explicit nonzero coefficient scale. -/
theorem exercise_15_10 [DecidableEq K]
    (firstFocus₁ firstFocus₂ secondFocus₁ secondFocus₂ : Point K)
    (firstAssociated secondAssociated : K)
    (firstPresentation :
      Presentation firstFocus₁ firstFocus₂ firstAssociated)
    (secondPresentation :
      Presentation secondFocus₁ secondFocus₂ secondAssociated)
    (eightNonzero : (8 : K) ≠ 0) (twoNonzero : (2 : K) ≠ 0)
    (noNegativeOneSquare : NoSquareRootOfNegativeOne (K := K))
    (scale : K) (scaleNonzero : scale ≠ 0)
    (sameConic :
      CoefficientScale
        (conic firstFocus₁ firstFocus₂ firstAssociated
          firstPresentation.associatedNonzero eightNonzero)
        (conic secondFocus₁ secondFocus₂ secondAssociated
          secondPresentation.associatedNonzero eightNonzero)
        scale) :
    firstAssociated = secondAssociated ∧
      ((firstFocus₁ = secondFocus₁ ∧ firstFocus₂ = secondFocus₂) ∨
        (firstFocus₁ = secondFocus₂ ∧ firstFocus₂ = secondFocus₁)) := by
  let firstConic :=
    conic firstFocus₁ firstFocus₂ firstAssociated
      firstPresentation.associatedNonzero eightNonzero
  let secondConic :=
    conic secondFocus₁ secondFocus₂ secondAssociated
      secondPresentation.associatedNonzero eightNonzero
  let firstMidpoint := midpoint firstFocus₁ firstFocus₂
  let secondMidpoint := midpoint secondFocus₁ secondFocus₂
  have firstDiscriminantNonzero : firstConic.centerDiscriminant ≠ 0 := by
    unfold firstConic
    exact conic_discriminant_nonzero firstFocus₁ firstFocus₂ firstAssociated
      firstPresentation eightNonzero
  have secondDiscriminantNonzero : secondConic.centerDiscriminant ≠ 0 := by
    unfold secondConic
    exact conic_discriminant_nonzero secondFocus₁ secondFocus₂
      secondAssociated secondPresentation eightNonzero
  have firstCenter : firstConic.IsCenter firstMidpoint := by
    unfold firstConic firstMidpoint
    exact conic_midpoint_isCenter firstFocus₁ firstFocus₂ firstAssociated
      firstPresentation.associatedNonzero eightNonzero twoNonzero
  have secondCenter : secondConic.IsCenter secondMidpoint := by
    unfold secondConic secondMidpoint
    exact conic_midpoint_isCenter secondFocus₁ secondFocus₂ secondAssociated
      secondPresentation.associatedNonzero eightNonzero twoNonzero
  have secondCenterForFirst : firstConic.IsCenter secondMidpoint :=
    sameConic.isCenter secondMidpoint secondCenter
  have firstCenterFormula := Conic.center_eq_centerPoint firstConic firstMidpoint
    firstDiscriminantNonzero firstCenter
  have secondCenterFormula := Conic.center_eq_centerPoint firstConic secondMidpoint
    firstDiscriminantNonzero secondCenterForFirst
  have midpointsEqual : firstMidpoint = secondMidpoint :=
    firstCenterFormula.trans secondCenterFormula.symm
  have firstCanonical :
      firstConic.centerDiscriminant =
        64 * firstConic.evaluate firstMidpoint := by
    unfold firstConic firstMidpoint
    rw [conic_centerDiscriminant firstFocus₁ firstFocus₂ firstAssociated
        firstPresentation.associatedNonzero eightNonzero,
      conic_evaluate_midpoint firstFocus₁ firstFocus₂ firstAssociated
        firstPresentation.associatedNonzero eightNonzero twoNonzero]
    ring1
  have secondCanonical :
      secondConic.centerDiscriminant =
        64 * secondConic.evaluate secondMidpoint := by
    unfold secondConic secondMidpoint
    rw [conic_centerDiscriminant secondFocus₁ secondFocus₂ secondAssociated
        secondPresentation.associatedNonzero eightNonzero,
      conic_evaluate_midpoint secondFocus₁ secondFocus₂ secondAssociated
        secondPresentation.associatedNonzero eightNonzero twoNonzero]
    ring1
  have discriminantScale := sameConic.discriminant
  have evaluationScale := sameConic.evaluate secondMidpoint
  have scaleDiscriminants :
      scale ^ 2 * secondConic.centerDiscriminant =
        scale * secondConic.centerDiscriminant := by
    calc
      scale ^ 2 * secondConic.centerDiscriminant =
          firstConic.centerDiscriminant := discriminantScale.symm
      _ = 64 * firstConic.evaluate firstMidpoint := firstCanonical
      _ = 64 * firstConic.evaluate secondMidpoint := by rw [midpointsEqual]
      _ = 64 * (scale * secondConic.evaluate secondMidpoint) := by
        rw [evaluationScale]
      _ = scale * (64 * secondConic.evaluate secondMidpoint) := by ring1
      _ = scale * secondConic.centerDiscriminant := by rw [secondCanonical]
  have discriminantTimesScaleDifference :
      secondConic.centerDiscriminant * (scale ^ 2 - scale) = 0 := by
    calc
      secondConic.centerDiscriminant * (scale ^ 2 - scale) =
          scale ^ 2 * secondConic.centerDiscriminant -
            scale * secondConic.centerDiscriminant := by ring1
      _ = 0 := by rw [scaleDiscriminants]; ring1
  have scalePolynomialZero := eq_zero_of_nonzero_mul_left
    secondDiscriminantNonzero discriminantTimesScaleDifference
  have scaleTimesDifference : scale * (scale - 1) = 0 := by
    calc
      scale * (scale - 1) = scale ^ 2 - scale := by ring1
      _ = 0 := scalePolynomialZero
  have scaleDifferenceZero :=
    eq_zero_of_nonzero_mul_left scaleNonzero scaleTimesDifference
  have scaleOne : scale = 1 := by
    calc
      scale = (scale - 1) + 1 := by ring1
      _ = 1 := by rw [scaleDifferenceZero]; ring1
  have dCoefficient : firstConic.d = secondConic.d := by
    calc
      firstConic.d = scale * secondConic.d := sameConic.d
      _ = secondConic.d := by rw [scaleOne]; ring1
  have eCoefficient : firstConic.e = secondConic.e := by
    calc
      firstConic.e = scale * secondConic.e := sameConic.e
      _ = secondConic.e := by rw [scaleOne]; ring1
  have fCoefficient : firstConic.f = secondConic.f := by
    calc
      firstConic.f = scale * secondConic.f := sameConic.f
      _ = secondConic.f := by rw [scaleOne]; ring1
  let firstX := firstFocus₂.x - firstFocus₁.x
  let firstY := firstFocus₂.y - firstFocus₁.y
  let secondX := secondFocus₂.x - secondFocus₁.x
  let secondY := secondFocus₂.y - secondFocus₁.y
  have fourNonzero := four_nonzero_of_eight_nonzero eightNonzero
  have negativeEightNonzero : (-8 : K) ≠ 0 := by
    intro negativeEightZero
    apply eightNonzero
    calc
      (8 : K) = -(-8) := by ring1
      _ = 0 := by rw [negativeEightZero]; ring1
  have dProductZero :
      (4 : K) * ((firstAssociated - firstX ^ 2) -
        (secondAssociated - secondX ^ 2)) = 0 := by
    calc
      (4 : K) * ((firstAssociated - firstX ^ 2) -
          (secondAssociated - secondX ^ 2)) =
        firstConic.d - secondConic.d := by
          unfold firstConic secondConic firstX secondX conic conicD
          ring1
      _ = 0 := by rw [dCoefficient]; ring1
  have eProductZero :
      (-8 : K) * (firstX * firstY - secondX * secondY) = 0 := by
    calc
      (-8 : K) * (firstX * firstY - secondX * secondY) =
        firstConic.e - secondConic.e := by
          unfold firstConic secondConic firstX firstY secondX secondY conic
            conicE
          ring1
      _ = 0 := by rw [eCoefficient]; ring1
  have fProductZero :
      (4 : K) * ((firstAssociated - firstY ^ 2) -
        (secondAssociated - secondY ^ 2)) = 0 := by
    calc
      (4 : K) * ((firstAssociated - firstY ^ 2) -
          (secondAssociated - secondY ^ 2)) =
        firstConic.f - secondConic.f := by
          unfold firstConic secondConic firstY secondY conic conicF
          ring1
      _ = 0 := by rw [fCoefficient]; ring1
  have dDifferenceZero :=
    eq_zero_of_nonzero_mul_left fourNonzero dProductZero
  have mixedDifferenceZero :=
    eq_zero_of_nonzero_mul_left negativeEightNonzero eProductZero
  have fDifferenceZero :=
    eq_zero_of_nonzero_mul_left fourNonzero fProductZero
  have dEqual :
      firstAssociated - firstX ^ 2 = secondAssociated - secondX ^ 2 := by
    calc
      firstAssociated - firstX ^ 2 =
          ((firstAssociated - firstX ^ 2) -
            (secondAssociated - secondX ^ 2)) +
              (secondAssociated - secondX ^ 2) := by ring1
      _ = secondAssociated - secondX ^ 2 := by
        rw [dDifferenceZero]
        ring1
  have mixedEqual : firstX * firstY = secondX * secondY := by
    calc
      firstX * firstY =
          (firstX * firstY - secondX * secondY) + secondX * secondY := by
        ring1
      _ = secondX * secondY := by rw [mixedDifferenceZero]; ring1
  have fEqual :
      firstAssociated - firstY ^ 2 = secondAssociated - secondY ^ 2 := by
    calc
      firstAssociated - firstY ^ 2 =
          ((firstAssociated - firstY ^ 2) -
            (secondAssociated - secondY ^ 2)) +
              (secondAssociated - secondY ^ 2) := by ring1
      _ = secondAssociated - secondY ^ 2 := by
        rw [fDifferenceZero]
        ring1
  have parameterUniqueness := parameters_unique_of_quadratic_coefficients
    firstX firstY secondX secondY firstAssociated secondAssociated
      noNegativeOneSquare dEqual mixedEqual fEqual
  refine ⟨parameterUniqueness.1, ?_⟩
  apply endpoint_pairs_of_midpoint_and_difference firstFocus₁ firstFocus₂
    secondFocus₁ secondFocus₂ twoNonzero midpointsEqual
  exact parameterUniqueness.2

/-- The first symmetric focus used in Examples 15.5 and 15.6. -/
def symmetricFirstFocus (a : K) : Point K := ⟨a, 0⟩

/-- The second symmetric focus used in Examples 15.5 and 15.6. -/
def symmetricSecondFocus (a : K) : Point K := ⟨-a, 0⟩

/-- Example 15.5: the quadrance between the displayed symmetric foci is
`4a²`. -/
theorem example_15_5_focus_quadrance (a : K) :
    quadrance (symmetricFirstFocus a) (symmetricSecondFocus a) =
      4 * a ^ 2 := by
  unfold symmetricFirstFocus symmetricSecondFocus quadrance
  ring1

/-- Example 15.5: expansion of the symmetric-focus quadrola gives exactly
the displayed diagonal conic equation. -/
theorem example_15_5_equation [DecidableEq K]
    (a associatedQuadrance : K)
    (associatedNonzero : associatedQuadrance ≠ 0)
    (eightNonzero : (8 : K) ≠ 0) (point : Point K) :
    (conic (symmetricFirstFocus a) (symmetricSecondFocus a)
      associatedQuadrance associatedNonzero eightNonzero).evaluate point =
        4 * (associatedQuadrance - 4 * a ^ 2) * point.x ^ 2 +
          4 * associatedQuadrance * point.y ^ 2 -
          associatedQuadrance * (associatedQuadrance - 4 * a ^ 2) := by
  unfold conic Conic.evaluate conicD conicE conicF conicA conicB conicC
    symmetricFirstFocus symmetricSecondFocus
  ring1

/-- Example 15.5: when `i²=-1`, exchanging the horizontal foci for the
displayed vertical foci and replacing `K` by `K-4a²` leaves the finite
Archimedes equation unchanged. -/
theorem example_15_5_alternate_foci
    (a associatedQuadrance i : K) (iSquare : i ^ 2 = -1)
    (point : Point K) :
    evaluate (symmetricFirstFocus a) (symmetricSecondFocus a)
        associatedQuadrance point =
      evaluate ⟨0, i * a⟩ ⟨0, -(i * a)⟩
        (associatedQuadrance - 4 * a ^ 2) point := by
  unfold evaluate
  simp only [archimedes_difference_identity]
  calc
    -(quadrance point (symmetricFirstFocus a) -
            quadrance point (symmetricSecondFocus a)) ^ 2 +
          2 * associatedQuadrance *
            (quadrance point (symmetricFirstFocus a) +
              quadrance point (symmetricSecondFocus a)) -
          associatedQuadrance ^ 2 =
        -16 * a ^ 2 * point.x ^ 2 +
          4 * associatedQuadrance *
            (point.x ^ 2 + point.y ^ 2 + a ^ 2) -
          associatedQuadrance ^ 2 := by
            unfold quadrance symmetricFirstFocus symmetricSecondFocus
            ring1
    _ = -16 * i ^ 2 * a ^ 2 * point.y ^ 2 +
          4 * (associatedQuadrance - 4 * a ^ 2) *
            (point.x ^ 2 + point.y ^ 2 + i ^ 2 * a ^ 2) -
          (associatedQuadrance - 4 * a ^ 2) ^ 2 := by
            rw [iSquare]
            ring1
    _ = -(quadrance point ⟨0, i * a⟩ -
            quadrance point ⟨0, -(i * a)⟩) ^ 2 +
          2 * (associatedQuadrance - 4 * a ^ 2) *
            (quadrance point ⟨0, i * a⟩ +
              quadrance point ⟨0, -(i * a)⟩) -
          (associatedQuadrance - 4 * a ^ 2) ^ 2 := by
            unfold quadrance
            ring1

/-- Example 15.5's alternate data satisfy all four quadrola nondegeneracy
clauses whenever the original symmetric data do. -/
theorem example_15_5_alternate_presentation
    (a associatedQuadrance i : K)
    (original :
      Presentation (symmetricFirstFocus a) (symmetricSecondFocus a)
        associatedQuadrance)
    (iSquare : i ^ 2 = -1) (eightNonzero : (8 : K) ≠ 0) :
    Presentation ⟨0, i * a⟩ ⟨0, -(i * a)⟩
      (associatedQuadrance - 4 * a ^ 2) := by
  have twoNonzero : (2 : K) ≠ 0 := by
    intro twoZero
    apply eightNonzero
    calc
      (8 : K) = 4 * 2 := by ring1
      _ = 0 := by rw [twoZero]; ring1
  have oneNonzero : (1 : K) ≠ 0 := by
    intro oneZero
    apply original.associatedNonzero
    calc
      associatedQuadrance = 1 * associatedQuadrance := by ring1
      _ = 0 := by rw [oneZero]; ring1
  have negativeOneNonzero : (-1 : K) ≠ 0 := by
    intro negativeOneZero
    apply oneNonzero
    calc
      (1 : K) = -(-1) := by ring1
      _ = 0 := by rw [negativeOneZero]; ring1
  have iNonzero : i ≠ 0 := by
    intro iZero
    apply negativeOneNonzero
    calc
      (-1 : K) = i ^ 2 := iSquare.symm
      _ = 0 := by rw [iZero]; ring1
  have aNonzero : a ≠ 0 := by
    intro aZero
    apply original.focusQuadranceNonzero
    rw [example_15_5_focus_quadrance, aZero]
    ring1
  have iaNonzero : i * a ≠ 0 :=
    RFAP.ExplicitField.mul_ne_zero iNonzero aNonzero
  have alternateFocusQuadrance :
      quadrance (⟨0, i * a⟩ : Point K) ⟨0, -(i * a)⟩ =
        -4 * a ^ 2 := by
    calc
      quadrance (⟨0, i * a⟩ : Point K) ⟨0, -(i * a)⟩ =
          4 * i ^ 2 * a ^ 2 := by
        unfold quadrance
        ring1
      _ = -4 * a ^ 2 := by rw [iSquare]; ring1
  constructor
  · intro equal
    have yEqual := congrArg Point.y equal
    change i * a = -(i * a) at yEqual
    have addedEqual := congrArg (fun value : K => value + i * a) yEqual
    have twiceIaZero : (2 : K) * (i * a) = 0 := by
      calc
        (2 : K) * (i * a) = i * a + i * a := by ring1
        _ = -(i * a) + i * a := addedEqual
        _ = 0 := by ring1
    exact (RFAP.ExplicitField.mul_ne_zero twoNonzero iaNonzero) twiceIaZero
  · intro associatedDifferenceZero
    apply original.focusQuadranceDifferent
    rw [example_15_5_focus_quadrance]
    calc
      4 * a ^ 2 = associatedQuadrance -
          (associatedQuadrance - 4 * a ^ 2) := by ring1
      _ = associatedQuadrance := by rw [associatedDifferenceZero]; ring1
  · intro alternateQuadranceZero
    apply original.focusQuadranceNonzero
    rw [example_15_5_focus_quadrance]
    calc
      4 * a ^ 2 = -(-4 * a ^ 2) := by ring1
      _ = -quadrance (⟨0, i * a⟩ : Point K) ⟨0, -(i * a)⟩ := by
        rw [alternateFocusQuadrance]
      _ = 0 := by rw [alternateQuadranceZero]; ring1
  · intro sameQuadrance
    apply original.associatedNonzero
    calc
      associatedQuadrance =
          (associatedQuadrance - 4 * a ^ 2) - (-4 * a ^ 2) := by ring1
      _ = quadrance (⟨0, i * a⟩ : Point K) ⟨0, -(i * a)⟩ -
          quadrance (⟨0, i * a⟩ : Point K) ⟨0, -(i * a)⟩ := by
        rw [← sameQuadrance, alternateFocusQuadrance]
      _ = 0 := by ring1

/-- Exercise 15.12: every quadrola conic is centered.  The midpoint of its
two displayed foci is an explicit center.  No nondegeneracy clause beyond
the one needed to construct the conic is used by this coefficient identity. -/
theorem exercise_15_12 [DecidableEq K]
    (firstFocus secondFocus : Point K) (associatedQuadrance : K)
    (associatedNonzero : associatedQuadrance ≠ 0)
    (eightNonzero : (8 : K) ≠ 0) (twoNonzero : (2 : K) ≠ 0) :
    (conic firstFocus secondFocus associatedQuadrance associatedNonzero
      eightNonzero).IsCenter (midpoint firstFocus secondFocus) := by
  exact conic_midpoint_isCenter firstFocus secondFocus associatedQuadrance
    associatedNonzero eightNonzero twoNonzero

private theorem conic_isAxis_of_fixed_foci [DecidableEq K]
    (firstFocus secondFocus : Point K) (associatedQuadrance : K)
    (associatedNonzero : associatedQuadrance ≠ 0)
    (eightNonzero : (8 : K) ≠ 0) (axis : Line K)
    (axisNonNull : ¬ axis.IsNull)
    (firstFixed : reflectPoint axis axisNonNull firstFocus = firstFocus)
    (secondFixed : reflectPoint axis axisNonNull secondFocus = secondFocus) :
    (conic firstFocus secondFocus associatedQuadrance associatedNonzero
      eightNonzero).IsAxis axis := by
  refine ⟨axisNonNull, ?_⟩
  intro point
  have firstQuadrance :
      quadrance (reflectPoint axis axisNonNull point) firstFocus =
        quadrance point firstFocus := by
    calc
      quadrance (reflectPoint axis axisNonNull point) firstFocus =
          quadrance (reflectPoint axis axisNonNull point)
            (reflectPoint axis axisNonNull firstFocus) := by rw [firstFixed]
      _ = quadrance point firstFocus :=
        reflectPoint_preserves_quadrance axis axisNonNull point firstFocus
  have secondQuadrance :
      quadrance (reflectPoint axis axisNonNull point) secondFocus =
        quadrance point secondFocus := by
    calc
      quadrance (reflectPoint axis axisNonNull point) secondFocus =
          quadrance (reflectPoint axis axisNonNull point)
            (reflectPoint axis axisNonNull secondFocus) := by rw [secondFixed]
      _ = quadrance point secondFocus :=
        reflectPoint_preserves_quadrance axis axisNonNull point secondFocus
  calc
    (conic firstFocus secondFocus associatedQuadrance associatedNonzero
          eightNonzero).evaluate (reflectPoint axis axisNonNull point) =
        evaluate firstFocus secondFocus associatedQuadrance
          (reflectPoint axis axisNonNull point) :=
      conic_evaluate firstFocus secondFocus associatedQuadrance associatedNonzero
        eightNonzero (reflectPoint axis axisNonNull point)
    _ = evaluate firstFocus secondFocus associatedQuadrance point := by
      unfold evaluate
      rw [firstQuadrance, secondQuadrance]
    _ = (conic firstFocus secondFocus associatedQuadrance associatedNonzero
          eightNonzero).evaluate point :=
      (conic_evaluate firstFocus secondFocus associatedQuadrance
        associatedNonzero eightNonzero point).symm

private theorem conic_isAxis_of_swapped_foci [DecidableEq K]
    (firstFocus secondFocus : Point K) (associatedQuadrance : K)
    (associatedNonzero : associatedQuadrance ≠ 0)
    (eightNonzero : (8 : K) ≠ 0) (axis : Line K)
    (axisNonNull : ¬ axis.IsNull)
    (firstToSecond : reflectPoint axis axisNonNull firstFocus = secondFocus)
    (secondToFirst : reflectPoint axis axisNonNull secondFocus = firstFocus) :
    (conic firstFocus secondFocus associatedQuadrance associatedNonzero
      eightNonzero).IsAxis axis := by
  refine ⟨axisNonNull, ?_⟩
  intro point
  have firstQuadrance :
      quadrance (reflectPoint axis axisNonNull point) firstFocus =
        quadrance point secondFocus := by
    calc
      quadrance (reflectPoint axis axisNonNull point) firstFocus =
          quadrance (reflectPoint axis axisNonNull point)
            (reflectPoint axis axisNonNull secondFocus) := by rw [secondToFirst]
      _ = quadrance point secondFocus :=
        reflectPoint_preserves_quadrance axis axisNonNull point secondFocus
  have secondQuadrance :
      quadrance (reflectPoint axis axisNonNull point) secondFocus =
        quadrance point firstFocus := by
    calc
      quadrance (reflectPoint axis axisNonNull point) secondFocus =
          quadrance (reflectPoint axis axisNonNull point)
            (reflectPoint axis axisNonNull firstFocus) := by rw [firstToSecond]
      _ = quadrance point firstFocus :=
        reflectPoint_preserves_quadrance axis axisNonNull point firstFocus
  calc
    (conic firstFocus secondFocus associatedQuadrance associatedNonzero
          eightNonzero).evaluate (reflectPoint axis axisNonNull point) =
        evaluate firstFocus secondFocus associatedQuadrance
          (reflectPoint axis axisNonNull point) :=
      conic_evaluate firstFocus secondFocus associatedQuadrance associatedNonzero
        eightNonzero (reflectPoint axis axisNonNull point)
    _ = evaluate firstFocus secondFocus associatedQuadrance point := by
      unfold evaluate
      rw [firstQuadrance, secondQuadrance]
      unfold archimedesFunction
      ring1
    _ = (conic firstFocus secondFocus associatedQuadrance associatedNonzero
          eightNonzero).evaluate point :=
      (conic_evaluate firstFocus secondFocus associatedQuadrance
        associatedNonzero eightNonzero point).symm

/-- Exercise 15.13: the focal line and the perpendicular bisector of the
foci are two inequivalent axes of every quadrola.  Both mirrors are proved
non-null from the definition's explicit nonzero focal quadrance. -/
theorem exercise_15_13 [DecidableEq K]
    (firstFocus secondFocus : Point K) (associatedQuadrance : K)
    (presentation : Presentation firstFocus secondFocus associatedQuadrance)
    (eightNonzero : (8 : K) ≠ 0) (twoNonzero : (2 : K) ≠ 0) :
    let focalAxis :=
      lineThrough firstFocus secondFocus presentation.fociDistinct
    let transverseAxis :=
      perpendicularBisector firstFocus secondFocus presentation.fociDistinct
    ¬ focalAxis.Equivalent transverseAxis ∧
      (conic firstFocus secondFocus associatedQuadrance
          presentation.associatedNonzero eightNonzero).IsAxis focalAxis ∧
      (conic firstFocus secondFocus associatedQuadrance
          presentation.associatedNonzero eightNonzero).IsAxis transverseAxis := by
  dsimp only
  let focalAxis :=
    lineThrough firstFocus secondFocus presentation.fociDistinct
  let transverseAxis :=
    perpendicularBisector firstFocus secondFocus presentation.fociDistinct
  have focalNonNull : ¬ focalAxis.IsNull := by
    intro focalNull
    apply presentation.focusQuadranceNonzero
    calc
      quadrance firstFocus secondFocus = lineNorm focalAxis := by
        unfold focalAxis
        exact (lineThrough_norm_eq_quadrance firstFocus secondFocus
          presentation.fociDistinct).symm
      _ = 0 := focalNull
  have transverseNonNull : ¬ transverseAxis.IsNull := by
    intro transverseNull
    apply presentation.focusQuadranceNonzero
    calc
      quadrance firstFocus secondFocus = lineNorm transverseAxis := by
        unfold transverseAxis perpendicularBisector lineNorm quadrance
        ring1
      _ = 0 := transverseNull
  have axesInequivalent : ¬ focalAxis.Equivalent transverseAxis := by
    intro equivalent
    apply presentation.focusQuadranceNonzero
    calc
      quadrance firstFocus secondFocus =
          focalAxis.a * transverseAxis.b -
            transverseAxis.a * focalAxis.b := by
        unfold focalAxis transverseAxis lineThrough perpendicularBisector
          quadrance
        ring1
      _ = 0 := by rw [equivalent.1]; ring1
  have firstFixed :
      reflectPoint focalAxis focalNonNull firstFocus = firstFocus := by
    apply reflectPoint_fixed_of_contains focalAxis focalNonNull firstFocus
    unfold focalAxis
    exact lineThrough_contains_first firstFocus secondFocus
      presentation.fociDistinct
  have secondFixed :
      reflectPoint focalAxis focalNonNull secondFocus = secondFocus := by
    apply reflectPoint_fixed_of_contains focalAxis focalNonNull secondFocus
    unfold focalAxis
    exact lineThrough_contains_second firstFocus secondFocus
      presentation.fociDistinct
  have firstToSecond :
      reflectPoint transverseAxis transverseNonNull firstFocus =
        secondFocus := by
    unfold transverseAxis
    exact reflectPoint_perpendicularBisector_first firstFocus secondFocus
      presentation.fociDistinct twoNonzero transverseNonNull
  have secondToFirst :
      reflectPoint transverseAxis transverseNonNull secondFocus =
        firstFocus := by
    unfold transverseAxis
    exact reflectPoint_perpendicularBisector_second firstFocus secondFocus
      presentation.fociDistinct twoNonzero transverseNonNull
  exact ⟨axesInequivalent,
    conic_isAxis_of_fixed_foci firstFocus secondFocus associatedQuadrance
      presentation.associatedNonzero eightNonzero focalAxis focalNonNull
      firstFixed secondFixed,
    conic_isAxis_of_swapped_foci firstFocus secondFocus associatedQuadrance
      presentation.associatedNonzero eightNonzero transverseAxis
      transverseNonNull firstToSecond secondToFirst⟩

/-- The first scalar coefficient in the quadrola gradient. -/
def firstWeight (firstQuadrance secondQuadrance associatedQuadrance : K) : K :=
  associatedQuadrance + secondQuadrance - firstQuadrance

/-- The second scalar coefficient in the quadrola gradient. -/
def secondWeight (firstQuadrance secondQuadrance associatedQuadrance : K) : K :=
  associatedQuadrance + firstQuadrance - secondQuadrance

/-- `x` coordinate of the gradient direction, after removing its common
factor four. -/
def tangentNormalX (firstFocus secondFocus : Point K)
    (associatedQuadrance : K) (point : Point K) : K :=
  let firstQuadrance := quadrance point firstFocus
  let secondQuadrance := quadrance point secondFocus
  firstWeight firstQuadrance secondQuadrance associatedQuadrance *
      (point.x - firstFocus.x) +
    secondWeight firstQuadrance secondQuadrance associatedQuadrance *
      (point.x - secondFocus.x)

/-- `y` coordinate of the same gradient direction. -/
def tangentNormalY (firstFocus secondFocus : Point K)
    (associatedQuadrance : K) (point : Point K) : K :=
  let firstQuadrance := quadrance point firstFocus
  let secondQuadrance := quadrance point secondFocus
  firstWeight firstQuadrance secondQuadrance associatedQuadrance *
      (point.y - firstFocus.y) +
    secondWeight firstQuadrance secondQuadrance associatedQuadrance *
      (point.y - secondFocus.y)

private theorem direction_nonzero_of_norm_nonzero [DecidableEq K]
    {first second : K} (normNonzero : first ^ 2 + second ^ 2 ≠ 0) :
    first ≠ 0 ∨ second ≠ 0 := by
  by_cases firstZero : first = 0
  · right
    intro secondZero
    apply normNonzero
    rw [firstZero, secondZero]
    ring1
  · exact Or.inl firstZero

/-- The gradient tangent representative used in Exercise 19.3. -/
def tangentLine [DecidableEq K]
    (firstFocus secondFocus : Point K) (associatedQuadrance : K)
    (point : Point K)
    (normalNonNull :
      tangentNormalX firstFocus secondFocus associatedQuadrance point ^ 2 +
        tangentNormalY firstFocus secondFocus associatedQuadrance point ^ 2 ≠
          0) : Line K where
  a := tangentNormalX firstFocus secondFocus associatedQuadrance point
  b := tangentNormalY firstFocus secondFocus associatedQuadrance point
  c := -(tangentNormalX firstFocus secondFocus associatedQuadrance point *
      point.x +
    tangentNormalY firstFocus secondFocus associatedQuadrance point * point.y)
  direction_nonzero := direction_nonzero_of_norm_nonzero normalNonNull

theorem tangentLine_contains [DecidableEq K]
    (firstFocus secondFocus : Point K) (associatedQuadrance : K)
    (point : Point K)
    (normalNonNull :
      tangentNormalX firstFocus secondFocus associatedQuadrance point ^ 2 +
        tangentNormalY firstFocus secondFocus associatedQuadrance point ^ 2 ≠
          0) :
    (tangentLine firstFocus secondFocus associatedQuadrance point
      normalNonNull).Contains point := by
  unfold tangentLine Line.Contains
  ring1

theorem tangentLine_nonNull [DecidableEq K]
    (firstFocus secondFocus : Point K) (associatedQuadrance : K)
    (point : Point K)
    (normalNonNull :
      tangentNormalX firstFocus secondFocus associatedQuadrance point ^ 2 +
        tangentNormalY firstFocus secondFocus associatedQuadrance point ^ 2 ≠
          0) :
    ¬ (tangentLine firstFocus secondFocus associatedQuadrance point
      normalNonNull).IsNull := by
  unfold tangentLine Line.IsNull
  exact normalNonNull

/-- The explicit conic gradient is four times the finite quadrola normal. -/
theorem conic_gradient [DecidableEq K]
    (firstFocus secondFocus : Point K) (associatedQuadrance : K)
    (associatedNonzero : associatedQuadrance ≠ 0)
    (eightNonzero : (8 : K) ≠ 0) (point : Point K) :
    let quadrolaConic := conic firstFocus secondFocus associatedQuadrance
      associatedNonzero eightNonzero
    quadrolaConic.a + 2 * quadrolaConic.d * point.x +
        quadrolaConic.e * point.y =
          4 * tangentNormalX firstFocus secondFocus associatedQuadrance point ∧
      quadrolaConic.b + quadrolaConic.e * point.x +
        2 * quadrolaConic.f * point.y =
          4 * tangentNormalY firstFocus secondFocus associatedQuadrance point := by
  dsimp only
  unfold conic conicD conicE conicF conicA conicB tangentNormalX
    tangentNormalY firstWeight secondWeight quadrance
  exact ⟨by ring1, by ring1⟩

/-- The gradient representative is the tangent line of the explicit conic,
up to the common factor four. -/
theorem tangentLine_formula [DecidableEq K]
    (firstFocus secondFocus : Point K) (associatedQuadrance : K)
    (associatedNonzero : associatedQuadrance ≠ 0)
    (eightNonzero : (8 : K) ≠ 0) (point : Point K)
    (onQuadrola : Contains firstFocus secondFocus associatedQuadrance point)
    (normalNonNull :
      tangentNormalX firstFocus secondFocus associatedQuadrance point ^ 2 +
        tangentNormalY firstFocus secondFocus associatedQuadrance point ^ 2 ≠
          0) :
    ∃ nonSingular :
        (conic firstFocus secondFocus associatedQuadrance associatedNonzero
          eightNonzero).IsNonSingularAt point,
      (Conic.tangentLine
        (conic firstFocus secondFocus associatedQuadrance associatedNonzero
          eightNonzero) point nonSingular).Equivalent
        (tangentLine firstFocus secondFocus associatedQuadrance point
          normalNonNull) := by
  let quadrolaConic := conic firstFocus secondFocus associatedQuadrance
    associatedNonzero eightNonzero
  let gradientLine := tangentLine firstFocus secondFocus associatedQuadrance
    point normalNonNull
  have gradient := conic_gradient firstFocus secondFocus associatedQuadrance
    associatedNonzero eightNonzero point
  have fourNonzero := four_nonzero_of_eight_nonzero eightNonzero
  have nonSingular : quadrolaConic.IsNonSingularAt point := by
    unfold Conic.IsNonSingularAt
    rw [gradient.1, gradient.2]
    rcases gradientLine.direction_nonzero with firstNonzero | secondNonzero
    · left
      exact RFAP.ExplicitField.mul_ne_zero fourNonzero firstNonzero
    · right
      exact RFAP.ExplicitField.mul_ne_zero fourNonzero secondNonzero
  have onConic : quadrolaConic.Contains point := by
    unfold Conic.Contains
    rw [conic_evaluate]
    exact onQuadrola
  let actualTangent := Conic.tangentLine quadrolaConic point nonSingular
  have actualContains : actualTangent.Contains point :=
    Conic.tangentLine_contains quadrolaConic point onConic nonSingular
  have firstCoefficient : actualTangent.a = 4 * gradientLine.a := by
    unfold actualTangent Conic.tangentLine gradientLine tangentLine
    exact gradient.1
  have secondCoefficient : actualTangent.b = 4 * gradientLine.b := by
    unfold actualTangent Conic.tangentLine gradientLine tangentLine
    exact gradient.2
  have constantCoefficient : actualTangent.c = 4 * gradientLine.c := by
    unfold Line.Contains at actualContains
    calc
      actualTangent.c =
          -(actualTangent.a * point.x + actualTangent.b * point.y) := by
        calc
          actualTangent.c =
              actualTangent.c -
                (actualTangent.a * point.x + actualTangent.b * point.y +
                  actualTangent.c) := by rw [actualContains]; ring1
          _ = -(actualTangent.a * point.x + actualTangent.b * point.y) := by
            ring1
      _ = -(4 * gradientLine.a * point.x +
          4 * gradientLine.b * point.y) := by
        rw [firstCoefficient, secondCoefficient]
      _ = 4 * gradientLine.c := by
        unfold gradientLine tangentLine
        ring1
  refine ⟨nonSingular, ?_⟩
  unfold Line.Equivalent
  rw [firstCoefficient, secondCoefficient, constantCoefficient]
  exact ⟨by ring1, by ring1, by ring1⟩

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
    _ = rightNumerator * (leftDenominator * leftDenominator⁻¹) *
        rightDenominator⁻¹ := by ring1
    _ = rightNumerator * rightDenominator⁻¹ := by
      rw [leftCancel]
      ring1

/-- Exercise 19.3 (Quadrola reflection).  The tangent makes equal spreads
with the two focal lines.  The three non-null hypotheses are exactly the
conditions required for those spreads to exist over a general field. -/
theorem reflection [DecidableEq K]
    (firstFocus secondFocus point : Point K) (associatedQuadrance : K)
    (pointFirstDistinct : point ≠ firstFocus)
    (pointSecondDistinct : point ≠ secondFocus)
    (onQuadrola : Contains firstFocus secondFocus associatedQuadrance point)
    (normalNonNull :
      tangentNormalX firstFocus secondFocus associatedQuadrance point ^ 2 +
        tangentNormalY firstFocus secondFocus associatedQuadrance point ^ 2 ≠
          0)
    (firstFocusLineNonNull :
      ¬ (lineThrough point firstFocus pointFirstDistinct).IsNull)
    (secondFocusLineNonNull :
      ¬ (lineThrough point secondFocus pointSecondDistinct).IsNull) :
    let tangent := tangentLine firstFocus secondFocus associatedQuadrance point
      normalNonNull
    spread tangent (lineThrough point firstFocus pointFirstDistinct)
        (tangentLine_nonNull firstFocus secondFocus associatedQuadrance point
          normalNonNull) firstFocusLineNonNull =
      spread tangent (lineThrough point secondFocus pointSecondDistinct)
        (tangentLine_nonNull firstFocus secondFocus associatedQuadrance point
          normalNonNull) secondFocusLineNonNull := by
  dsimp only
  let firstQuadrance := quadrance point firstFocus
  let secondQuadrance := quadrance point secondFocus
  let firstCoefficient :=
    firstWeight firstQuadrance secondQuadrance associatedQuadrance
  let secondCoefficient :=
    secondWeight firstQuadrance secondQuadrance associatedQuadrance
  let firstX := point.x - firstFocus.x
  let firstY := point.y - firstFocus.y
  let secondX := point.x - secondFocus.x
  let secondY := point.y - secondFocus.y
  let mixedProduct := firstX * secondX + firstY * secondY
  let normalX := tangentNormalX firstFocus secondFocus associatedQuadrance point
  let normalY := tangentNormalY firstFocus secondFocus associatedQuadrance point
  let firstDot := normalX * firstX + normalY * firstY
  let secondDot := normalX * secondX + normalY * secondY
  have firstQuadranceFormula :
      firstQuadrance = firstX ^ 2 + firstY ^ 2 := by
    unfold firstQuadrance firstX firstY quadrance
    ring1
  have secondQuadranceFormula :
      secondQuadrance = secondX ^ 2 + secondY ^ 2 := by
    unfold secondQuadrance secondX secondY quadrance
    ring1
  have firstCoefficientSquare :
      firstCoefficient ^ 2 =
        4 * associatedQuadrance * secondQuadrance := by
    unfold Contains evaluate at onQuadrola
    have differenceZero :
        firstCoefficient ^ 2 -
          4 * associatedQuadrance * secondQuadrance = 0 := by
      calc
        firstCoefficient ^ 2 -
            4 * associatedQuadrance * secondQuadrance =
          -(archimedesFunction firstQuadrance secondQuadrance
            associatedQuadrance) := by
          unfold firstCoefficient firstWeight archimedesFunction
          ring1
        _ = 0 := by rw [onQuadrola]; ring1
    exact sub_eq_zero.mp differenceZero
  have secondCoefficientSquare :
      secondCoefficient ^ 2 =
        4 * associatedQuadrance * firstQuadrance := by
    unfold Contains evaluate at onQuadrola
    have differenceZero :
        secondCoefficient ^ 2 -
          4 * associatedQuadrance * firstQuadrance = 0 := by
      calc
        secondCoefficient ^ 2 -
            4 * associatedQuadrance * firstQuadrance =
          -(archimedesFunction firstQuadrance secondQuadrance
            associatedQuadrance) := by
          unfold secondCoefficient secondWeight archimedesFunction
          ring1
        _ = 0 := by rw [onQuadrola]; ring1
    exact sub_eq_zero.mp differenceZero
  have normalXFormula :
      normalX = firstCoefficient * firstX + secondCoefficient * secondX := by
    unfold normalX tangentNormalX firstCoefficient secondCoefficient
      firstQuadrance secondQuadrance firstX secondX
    rfl
  have normalYFormula :
      normalY = firstCoefficient * firstY + secondCoefficient * secondY := by
    unfold normalY tangentNormalY firstCoefficient secondCoefficient
      firstQuadrance secondQuadrance firstY secondY
    rfl
  have firstDotFormula :
      firstDot = firstCoefficient * firstQuadrance +
        secondCoefficient * mixedProduct := by
    unfold firstDot mixedProduct
    rw [normalXFormula, normalYFormula, firstQuadranceFormula]
    ring1
  have secondDotFormula :
      secondDot = firstCoefficient * mixedProduct +
        secondCoefficient * secondQuadrance := by
    unfold secondDot mixedProduct
    rw [normalXFormula, normalYFormula, secondQuadranceFormula]
    ring1
  have dotCrossProduct :
      firstDot ^ 2 * secondQuadrance =
        secondDot ^ 2 * firstQuadrance := by
    rw [firstDotFormula, secondDotFormula]
    calc
      (firstCoefficient * firstQuadrance +
            secondCoefficient * mixedProduct) ^ 2 * secondQuadrance =
        (firstCoefficient * mixedProduct +
            secondCoefficient * secondQuadrance) ^ 2 * firstQuadrance +
          (firstQuadrance * secondQuadrance - mixedProduct ^ 2) *
            (firstCoefficient ^ 2 * firstQuadrance -
              secondCoefficient ^ 2 * secondQuadrance) := by ring1
      _ = (firstCoefficient * mixedProduct +
          secondCoefficient * secondQuadrance) ^ 2 * firstQuadrance := by
        rw [firstCoefficientSquare, secondCoefficientSquare]
        ring1
  let tangent := tangentLine firstFocus secondFocus associatedQuadrance point
    normalNonNull
  let firstLine := lineThrough point firstFocus pointFirstDistinct
  let secondLine := lineThrough point secondFocus pointSecondDistinct
  have firstNumerator :
      (tangent.a * firstLine.b - firstLine.a * tangent.b) ^ 2 =
        firstDot ^ 2 := by
    unfold tangent tangentLine firstLine lineThrough firstDot normalX normalY
      firstX firstY
    ring1
  have secondNumerator :
      (tangent.a * secondLine.b - secondLine.a * tangent.b) ^ 2 =
        secondDot ^ 2 := by
    unfold tangent tangentLine secondLine lineThrough secondDot normalX normalY
      secondX secondY
    ring1
  have firstNorm : lineNorm firstLine = firstQuadrance := by
    unfold firstLine firstQuadrance
    exact lineThrough_norm_eq_quadrance point firstFocus pointFirstDistinct
  have secondNorm : lineNorm secondLine = secondQuadrance := by
    unfold secondLine secondQuadrance
    exact lineThrough_norm_eq_quadrance point secondFocus pointSecondDistinct
  have tangentNonNull := tangentLine_nonNull firstFocus secondFocus
    associatedQuadrance point normalNonNull
  have firstDenominatorNonzero :
      lineNorm tangent * lineNorm firstLine ≠ 0 :=
    RFAP.ExplicitField.mul_ne_zero tangentNonNull firstFocusLineNonNull
  have secondDenominatorNonzero :
      lineNorm tangent * lineNorm secondLine ≠ 0 :=
    RFAP.ExplicitField.mul_ne_zero tangentNonNull secondFocusLineNonNull
  have firstDenominatorNonzero' :
      lineNorm tangent * firstQuadrance ≠ 0 := by
    rw [← firstNorm]
    exact firstDenominatorNonzero
  have secondDenominatorNonzero' :
      lineNorm tangent * secondQuadrance ≠ 0 := by
    rw [← secondNorm]
    exact secondDenominatorNonzero
  unfold spread
  rw [firstNumerator, secondNumerator, firstNorm, secondNorm]
  change
    firstDot ^ 2 / (lineNorm tangent * firstQuadrance) =
      secondDot ^ 2 / (lineNorm tangent * secondQuadrance)
  apply div_eq_div_of_cross_mul firstDenominatorNonzero'
    secondDenominatorNonzero'
  calc
    firstDot ^ 2 * (lineNorm tangent * secondQuadrance) =
        lineNorm tangent * (firstDot ^ 2 * secondQuadrance) := by ring1
    _ = lineNorm tangent * (secondDot ^ 2 * firstQuadrance) := by
      rw [dotCrossProduct]
    _ = secondDot ^ 2 * (lineNorm tangent * firstQuadrance) := by ring1

end Quadrola

end DivineProportions
