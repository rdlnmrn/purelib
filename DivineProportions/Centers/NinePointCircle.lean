import DivineProportions.Centers.EulerLine
import DivineProportions.Conics.Circle
import DivineProportions.Triangles.Right

/-!
# Divine Proportions, Theorem 117: the nine point circle

All nine points and the circle are explicit finite constructions.  The six
midpoint incidences follow from the cleared Euler relation `2C+O=A₁+A₂+A₃`.
For an altitude foot, the side-midpoint and vertex--orthocenter midpoint form
a diameter: a denominator-cleared dot-product lemma supplies the right-angle
calculation even when the foot coincides with a diameter endpoint.
-/

namespace DivineProportions

variable {K : Type*} [RFAP.ExplicitField K]

/-- The midpoint of the side opposite the first vertex. -/
def sideMidpointOppositeFirst (_first second third : Point K) : Point K :=
  midpoint second third

/-- The midpoint of the side opposite the second vertex. -/
def sideMidpointOppositeSecond (first _second third : Point K) : Point K :=
  midpoint first third

/-- The midpoint of the side opposite the third vertex. -/
def sideMidpointOppositeThird (first second _third : Point K) : Point K :=
  midpoint first second

/-- The midpoint of a vertex and the displayed orthocenter. -/
def vertexOrthocenterMidpoint (vertex orthocenter : Point K) : Point K :=
  midpoint vertex orthocenter

/-- Exercise 18.2's nine-point center, the midpoint of circumcenter and
orthocenter. -/
def ninePointCenter (circumcenter orthocenter : Point K) : Point K :=
  midpoint circumcenter orthocenter

/-- The explicit circle used in Theorem 117. -/
def ninePointCircle
    [Nontrivial K]
    (circumcenter orthocenter : Point K) (circleQuadrance : K) : Conic K :=
  Conic.circleConic (ninePointCenter circumcenter orthocenter)
    circleQuadrance

/-- The bracket-numerator coordinate formula printed in Exercise 18.2. -/
def ninePointCenterFormula (first second third : Point K) : Point K :=
  let denominator := antisymmetricTripleProduct
    first.x second.x third.x first.y second.y third.y
  ⟨(circumcenterXNumerator first second third +
      2 * orthocenterXNumerator first second third) / (4 * denominator),
    (circumcenterYNumerator first second third +
      2 * orthocenterYNumerator first second third) / (4 * denominator)⟩

private theorem eq_of_mul_eq_mul_right
    {left right factor : K} (factorNonzero : factor ≠ 0)
    (productsEqual : left * factor = right * factor) : left = right := by
  have factorCancel : factor * factor⁻¹ = (1 : K) :=
    RFAP.ExplicitField.mul_inv_cancel factor factorNonzero
  calc
    left = left * 1 := by ring1
    _ = left * (factor * factor⁻¹) := by rw [factorCancel]
    _ = (left * factor) * factor⁻¹ := by ring1
    _ = (right * factor) * factor⁻¹ := by rw [productsEqual]
    _ = right * (factor * factor⁻¹) := by ring1
    _ = right := by rw [factorCancel]; ring1

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

/-- Exercise 18.2's coordinate calculation: the midpoint of the displayed
circumcenter and orthocenter is exactly the printed bracket formula. -/
theorem exercise_18_2_formula
    [Nontrivial K] [DecidableEq K]
    (first second third : Point K)
    (firstThirdDistinct : first ≠ third)
    (secondThirdDistinct : second ≠ third)
    (notCollinear : ¬ Collinear first second third)
    (twoNonzero : (2 : K) ≠ 0) :
    ninePointCenter
        (circumcenterPoint first second third firstThirdDistinct
          secondThirdDistinct notCollinear)
        (orthocenterPoint first second third firstThirdDistinct
          secondThirdDistinct notCollinear) =
      ninePointCenterFormula first second third := by
  rw [circumcenter_formula first second third firstThirdDistinct
    secondThirdDistinct notCollinear twoNonzero]
  rw [orthocenter_formula first second third firstThirdDistinct
    secondThirdDistinct notCollinear]
  let denominator := antisymmetricTripleProduct
    first.x second.x third.x first.y second.y third.y
  let circumcenterX := circumcenterXNumerator first second third
  let circumcenterY := circumcenterYNumerator first second third
  let orthocenterX := orthocenterXNumerator first second third
  let orthocenterY := orthocenterYNumerator first second third
  have denominatorEqualsDeterminant :
      denominator = pointDeterminant first second third := by
    exact (pointDeterminant_eq_antisymmetricTripleProduct
      first second third).symm
  have denominatorNonzero : denominator ≠ 0 := by
    rw [denominatorEqualsDeterminant]
    intro determinantZero
    apply notCollinear
    exact (collinear_iff_pointDeterminant_eq_zero first second third).2
      determinantZero
  have twiceDenominatorNonzero : 2 * denominator ≠ 0 :=
    RFAP.ExplicitField.mul_ne_zero twoNonzero denominatorNonzero
  have fourNonzero : (4 : K) ≠ 0 := by
    have productNonzero :=
      RFAP.ExplicitField.mul_ne_zero twoNonzero twoNonzero
    simpa only [show (4 : K) = 2 * 2 by ring1] using productNonzero
  have fourDenominatorNonzero : 4 * denominator ≠ 0 :=
    RFAP.ExplicitField.mul_ne_zero fourNonzero denominatorNonzero
  apply Point.ext
  · change ((circumcenterX / (2 * denominator) +
          orthocenterX / denominator) / 2) =
        (circumcenterX + 2 * orthocenterX) / (4 * denominator)
    apply eq_of_mul_eq_mul_right fourDenominatorNonzero
    calc
      ((circumcenterX / (2 * denominator) + orthocenterX / denominator) /
          2) * (4 * denominator) =
        (circumcenterX / (2 * denominator)) * (2 * denominator) +
          2 * ((orthocenterX / denominator) * denominator) := by
            simp only [RFAP.ExplicitField.div_eq_mul_inv]
            have twoCancel : (2 : K) * (2 : K)⁻¹ = 1 :=
              RFAP.ExplicitField.mul_inv_cancel 2 twoNonzero
            rw [show (4 : K) = 2 * 2 by ring1]
            calc
              (circumcenterX * (2 * denominator)⁻¹ +
                    orthocenterX * denominator⁻¹) * 2⁻¹ *
                  (2 * 2 * denominator) =
                (2 * 2⁻¹) *
                  (circumcenterX * (2 * denominator)⁻¹ *
                      (2 * denominator) +
                    2 * (orthocenterX * denominator⁻¹ * denominator)) := by
                      ring1
              _ = _ := by rw [twoCancel]; ring1
      _ = circumcenterX + 2 * orthocenterX := by
        rw [RFAP.ExplicitField.div_mul_cancel circumcenterX
            twiceDenominatorNonzero,
          RFAP.ExplicitField.div_mul_cancel orthocenterX denominatorNonzero]
      _ = ((circumcenterX + 2 * orthocenterX) / (4 * denominator)) *
          (4 * denominator) := by
        exact (RFAP.ExplicitField.div_mul_cancel _
          fourDenominatorNonzero).symm
  · change ((circumcenterY / (2 * denominator) +
          orthocenterY / denominator) / 2) =
        (circumcenterY + 2 * orthocenterY) / (4 * denominator)
    apply eq_of_mul_eq_mul_right fourDenominatorNonzero
    calc
      ((circumcenterY / (2 * denominator) + orthocenterY / denominator) /
          2) * (4 * denominator) =
        (circumcenterY / (2 * denominator)) * (2 * denominator) +
          2 * ((orthocenterY / denominator) * denominator) := by
            simp only [RFAP.ExplicitField.div_eq_mul_inv]
            have twoCancel : (2 : K) * (2 : K)⁻¹ = 1 :=
              RFAP.ExplicitField.mul_inv_cancel 2 twoNonzero
            rw [show (4 : K) = 2 * 2 by ring1]
            calc
              (circumcenterY * (2 * denominator)⁻¹ +
                    orthocenterY * denominator⁻¹) * 2⁻¹ *
                  (2 * 2 * denominator) =
                (2 * 2⁻¹) *
                  (circumcenterY * (2 * denominator)⁻¹ *
                      (2 * denominator) +
                    2 * (orthocenterY * denominator⁻¹ * denominator)) := by
                      ring1
              _ = _ := by rw [twoCancel]; ring1
      _ = circumcenterY + 2 * orthocenterY := by
        rw [RFAP.ExplicitField.div_mul_cancel circumcenterY
            twiceDenominatorNonzero,
          RFAP.ExplicitField.div_mul_cancel orthocenterY denominatorNonzero]
      _ = ((circumcenterY + 2 * orthocenterY) / (4 * denominator)) *
          (4 * denominator) := by
        exact (RFAP.ExplicitField.div_mul_cancel _
          fourDenominatorNonzero).symm

/-- Exercise 18.2's deduction: the nine-point center is the midpoint of
`OC`, hence is collinear with the two Euler-line centers. -/
theorem exercise_18_2_center_on_euler_line
    [Nontrivial K] [DecidableEq K]
    (circumcenter orthocenter : Point K)
    (twoNonzero : (2 : K) ≠ 0) :
    Collinear circumcenter orthocenter
      (ninePointCenter circumcenter orthocenter) := by
  have weightsSum : (1 / 2 : K) + 1 / 2 = 1 := by
    apply eq_of_mul_eq_mul_right twoNonzero
    calc
      ((1 / 2 : K) + 1 / 2) * 2 =
          (1 / 2 : K) * 2 + (1 / 2 : K) * 2 := by ring1
      _ = 1 + 1 := by
        rw [RFAP.ExplicitField.div_mul_cancel 1 twoNonzero]
      _ = 1 * 2 := by ring1
  have result := collinear_affineCombination circumcenter orthocenter
    ((1 : K) / 2) ((1 : K) / 2) weightsSum
  have midpointEquals :
      affineCombination ((1 : K) / 2) circumcenter ((1 : K) / 2)
          orthocenter = ninePointCenter circumcenter orthocenter := by
    apply Point.ext <;>
      simp only [affineCombination, ninePointCenter, midpoint,
        RFAP.ExplicitField.div_eq_mul_inv] <;> ring1
  rw [midpointEquals] at result
  exact result

/-- Any displayed line containing two points also contains their midpoint. -/
theorem line_contains_midpoint
    (line : Line K) (first second : Point K)
    (twoNonzero : (2 : K) ≠ 0)
    (containsFirst : line.Contains first)
    (containsSecond : line.Contains second) :
    line.Contains (midpoint first second) := by
  unfold Line.Contains at containsFirst containsSecond ⊢
  apply eq_of_mul_eq_mul_right twoNonzero
  calc
    (line.a * (midpoint first second).x +
          line.b * (midpoint first second).y + line.c) * 2 =
      (line.a * first.x + line.b * first.y + line.c) +
        (line.a * second.x + line.b * second.y + line.c) := by
          change (line.a * ((first.x + second.x) / 2) +
            line.b * ((first.y + second.y) / 2) + line.c) * 2 = _
          calc
            (line.a * ((first.x + second.x) / 2) +
                line.b * ((first.y + second.y) / 2) + line.c) * 2 =
              line.a * (((first.x + second.x) / 2) * 2) +
                line.b * (((first.y + second.y) / 2) * 2) +
                line.c * 2 := by ring1
            _ = _ := by
              rw [RFAP.ExplicitField.div_mul_cancel _ twoNonzero,
                RFAP.ExplicitField.div_mul_cancel _ twoNonzero]
              ring1
    _ = 0 := by rw [containsFirst, containsSecond]; ring1
    _ = 0 * 2 := by ring1

/-- The midpoint pair belonging to one vertex has the common nine-point
center and the expected endpoint quadrances. -/
theorem ninePoint_midpoint_pair
    [DecidableEq K]
    (vertex sideFirst sideSecond circumcenter orthocenter : Point K)
    (twoNonzero : (2 : K) ≠ 0)
    (centerX : 2 * circumcenter.x + orthocenter.x =
      vertex.x + sideFirst.x + sideSecond.x)
    (centerY : 2 * circumcenter.y + orthocenter.y =
      vertex.y + sideFirst.y + sideSecond.y) :
    let sideMidpoint := midpoint sideFirst sideSecond
    let oppositeMidpoint := midpoint vertex orthocenter
    let center := ninePointCenter circumcenter orthocenter
    midpoint sideMidpoint oppositeMidpoint = center ∧
      quadrance center sideMidpoint = quadrance circumcenter vertex / 4 ∧
      quadrance center oppositeMidpoint = quadrance circumcenter vertex / 4 := by
  dsimp only [ninePointCenter]
  let sideMidpoint := midpoint sideFirst sideSecond
  let oppositeMidpoint := midpoint vertex orthocenter
  let center := midpoint circumcenter orthocenter
  have fourNonzero : (4 : K) ≠ 0 := by
    have productNonzero :=
      RFAP.ExplicitField.mul_ne_zero twoNonzero twoNonzero
    simpa only [show (4 : K) = 2 * 2 by ring1] using productNonzero
  have midpointSumX :
      sideMidpoint.x + oppositeMidpoint.x =
        circumcenter.x + orthocenter.x := by
    apply eq_of_mul_eq_mul_right twoNonzero
    calc
      (sideMidpoint.x + oppositeMidpoint.x) * 2 =
          sideFirst.x + sideSecond.x + vertex.x + orthocenter.x := by
        change (((sideFirst.x + sideSecond.x) / 2) +
          ((vertex.x + orthocenter.x) / 2)) * 2 = _
        calc
          (((sideFirst.x + sideSecond.x) / 2) +
              ((vertex.x + orthocenter.x) / 2)) * 2 =
            ((sideFirst.x + sideSecond.x) / 2) * 2 +
              ((vertex.x + orthocenter.x) / 2) * 2 := by ring1
          _ = _ := by
            rw [RFAP.ExplicitField.div_mul_cancel _ twoNonzero,
              RFAP.ExplicitField.div_mul_cancel _ twoNonzero]
            ring1
      _ = (circumcenter.x + orthocenter.x) * 2 := by
        calc
          sideFirst.x + sideSecond.x + vertex.x + orthocenter.x =
              (vertex.x + sideFirst.x + sideSecond.x) + orthocenter.x := by
            ring1
          _ = (2 * circumcenter.x + orthocenter.x) + orthocenter.x := by
            rw [← centerX]
          _ = (circumcenter.x + orthocenter.x) * 2 := by ring1
  have midpointSumY :
      sideMidpoint.y + oppositeMidpoint.y =
        circumcenter.y + orthocenter.y := by
    apply eq_of_mul_eq_mul_right twoNonzero
    calc
      (sideMidpoint.y + oppositeMidpoint.y) * 2 =
          sideFirst.y + sideSecond.y + vertex.y + orthocenter.y := by
        change (((sideFirst.y + sideSecond.y) / 2) +
          ((vertex.y + orthocenter.y) / 2)) * 2 = _
        calc
          (((sideFirst.y + sideSecond.y) / 2) +
              ((vertex.y + orthocenter.y) / 2)) * 2 =
            ((sideFirst.y + sideSecond.y) / 2) * 2 +
              ((vertex.y + orthocenter.y) / 2) * 2 := by ring1
          _ = _ := by
            rw [RFAP.ExplicitField.div_mul_cancel _ twoNonzero,
              RFAP.ExplicitField.div_mul_cancel _ twoNonzero]
            ring1
      _ = (circumcenter.y + orthocenter.y) * 2 := by
        calc
          sideFirst.y + sideSecond.y + vertex.y + orthocenter.y =
              (vertex.y + sideFirst.y + sideSecond.y) + orthocenter.y := by
            ring1
          _ = (2 * circumcenter.y + orthocenter.y) + orthocenter.y := by
            rw [← centerY]
          _ = (circumcenter.y + orthocenter.y) * 2 := by ring1
  have pairCenter : midpoint sideMidpoint oppositeMidpoint = center := by
    apply Point.ext
    · change (sideMidpoint.x + oppositeMidpoint.x) / 2 =
          (circumcenter.x + orthocenter.x) / 2
      rw [midpointSumX]
    · change (sideMidpoint.y + oppositeMidpoint.y) / 2 =
          (circumcenter.y + orthocenter.y) / 2
      rw [midpointSumY]
  have displacementX :
      sideMidpoint.x - oppositeMidpoint.x = circumcenter.x - vertex.x := by
    apply eq_of_mul_eq_mul_right twoNonzero
    calc
      (sideMidpoint.x - oppositeMidpoint.x) * 2 =
          sideFirst.x + sideSecond.x - vertex.x - orthocenter.x := by
        change (((sideFirst.x + sideSecond.x) / 2) -
          ((vertex.x + orthocenter.x) / 2)) * 2 = _
        calc
          (((sideFirst.x + sideSecond.x) / 2) -
              ((vertex.x + orthocenter.x) / 2)) * 2 =
            ((sideFirst.x + sideSecond.x) / 2) * 2 -
              ((vertex.x + orthocenter.x) / 2) * 2 := by ring1
          _ = _ := by
            rw [RFAP.ExplicitField.div_mul_cancel _ twoNonzero,
              RFAP.ExplicitField.div_mul_cancel _ twoNonzero]
            ring1
      _ = (circumcenter.x - vertex.x) * 2 := by
        calc
          sideFirst.x + sideSecond.x - vertex.x - orthocenter.x =
              (vertex.x + sideFirst.x + sideSecond.x) -
                2 * vertex.x - orthocenter.x := by ring1
          _ = (2 * circumcenter.x + orthocenter.x) -
                2 * vertex.x - orthocenter.x := by rw [← centerX]
          _ = (circumcenter.x - vertex.x) * 2 := by ring1
  have displacementY :
      sideMidpoint.y - oppositeMidpoint.y = circumcenter.y - vertex.y := by
    apply eq_of_mul_eq_mul_right twoNonzero
    calc
      (sideMidpoint.y - oppositeMidpoint.y) * 2 =
          sideFirst.y + sideSecond.y - vertex.y - orthocenter.y := by
        change (((sideFirst.y + sideSecond.y) / 2) -
          ((vertex.y + orthocenter.y) / 2)) * 2 = _
        calc
          (((sideFirst.y + sideSecond.y) / 2) -
              ((vertex.y + orthocenter.y) / 2)) * 2 =
            ((sideFirst.y + sideSecond.y) / 2) * 2 -
              ((vertex.y + orthocenter.y) / 2) * 2 := by ring1
          _ = _ := by
            rw [RFAP.ExplicitField.div_mul_cancel _ twoNonzero,
              RFAP.ExplicitField.div_mul_cancel _ twoNonzero]
            ring1
      _ = (circumcenter.y - vertex.y) * 2 := by
        calc
          sideFirst.y + sideSecond.y - vertex.y - orthocenter.y =
              (vertex.y + sideFirst.y + sideSecond.y) -
                2 * vertex.y - orthocenter.y := by ring1
          _ = (2 * circumcenter.y + orthocenter.y) -
                2 * vertex.y - orthocenter.y := by rw [← centerY]
          _ = (circumcenter.y - vertex.y) * 2 := by ring1
  have pairQuadrance :
      quadrance sideMidpoint oppositeMidpoint =
        quadrance circumcenter vertex := by
    unfold quadrance
    calc
      (oppositeMidpoint.x - sideMidpoint.x) ^ 2 +
          (oppositeMidpoint.y - sideMidpoint.y) ^ 2 =
        (sideMidpoint.x - oppositeMidpoint.x) ^ 2 +
          (sideMidpoint.y - oppositeMidpoint.y) ^ 2 := by ring1
      _ = (circumcenter.x - vertex.x) ^ 2 +
          (circumcenter.y - vertex.y) ^ 2 := by
        rw [displacementX, displacementY]
      _ = (vertex.x - circumcenter.x) ^ 2 +
          (vertex.y - circumcenter.y) ^ 2 := by ring1
  have sideQuadrance := midpoint_quadrance
    sideMidpoint oppositeMidpoint twoNonzero
  rw [pairCenter, pairQuadrance] at sideQuadrance
  have equalEndpointQuadrances := midpoint_equal_quadrance
    sideMidpoint oppositeMidpoint twoNonzero
  rw [pairCenter] at equalEndpointQuadrances
  exact ⟨pairCenter, sideQuadrance,
    equalEndpointQuadrances.symm.trans sideQuadrance⟩

/-- The dot product of the two vectors based at `origin`. -/
def pointVectorDot (origin first second : Point K) : K :=
  (first.x - origin.x) * (second.x - origin.x) +
    (first.y - origin.y) * (second.y - origin.y)

/-- A vector along a non-null line is perpendicular to a vector along an
altitude to that line. -/
theorem pointVectorDot_eq_zero_of_line_altitude
    (line : Line K) (altitudeSource sidePoint altitudePoint foot : Point K)
    (lineNonNull : ¬ line.IsNull)
    (sideOnLine : line.Contains sidePoint)
    (footOnLine : line.Contains foot)
    (altitudeOnLine : (altitudeThrough altitudeSource line).Contains altitudePoint)
    (footOnAltitude : (altitudeThrough altitudeSource line).Contains foot) :
    pointVectorDot foot sidePoint altitudePoint = 0 := by
  have sideEquation :
      line.a * (sidePoint.x - foot.x) +
        line.b * (sidePoint.y - foot.y) = 0 := by
    unfold Line.Contains at sideOnLine footOnLine
    calc
      line.a * (sidePoint.x - foot.x) +
          line.b * (sidePoint.y - foot.y) =
        (line.a * sidePoint.x + line.b * sidePoint.y + line.c) -
          (line.a * foot.x + line.b * foot.y + line.c) := by ring1
      _ = 0 := by rw [sideOnLine, footOnLine]; ring1
  have altitudeEquation :
      -line.b * (altitudePoint.x - foot.x) +
        line.a * (altitudePoint.y - foot.y) = 0 := by
    unfold altitudeThrough Line.Contains at altitudeOnLine footOnAltitude
    calc
      -line.b * (altitudePoint.x - foot.x) +
          line.a * (altitudePoint.y - foot.y) =
        (-line.b * altitudePoint.x + line.a * altitudePoint.y +
            (line.b * altitudeSource.x - line.a * altitudeSource.y)) -
          (-line.b * foot.x + line.a * foot.y +
            (line.b * altitudeSource.x - line.a * altitudeSource.y)) := by ring1
      _ = 0 := by rw [altitudeOnLine, footOnAltitude]; ring1
  apply eq_zero_of_mul_eq_zero_left lineNonNull
  calc
    lineNorm line * pointVectorDot foot sidePoint altitudePoint =
      (line.a * (sidePoint.x - foot.x) +
          line.b * (sidePoint.y - foot.y)) *
        (line.a * (altitudePoint.x - foot.x) +
          line.b * (altitudePoint.y - foot.y)) +
      (-line.b * (sidePoint.x - foot.x) +
          line.a * (sidePoint.y - foot.y)) *
        (-line.b * (altitudePoint.x - foot.x) +
          line.a * (altitudePoint.y - foot.y)) := by
            unfold lineNorm pointVectorDot
            ring1
    _ = 0 := by rw [sideEquation, altitudeEquation]; ring1

/-- A right vertex has the same quadrance from the midpoint as either
endpoint, without any distinctness premise on the three points. -/
theorem midpoint_right_quadrance_of_dot_zero
    [DecidableEq K]
    (first second rightVertex : Point K)
    (twoNonzero : (2 : K) ≠ 0)
    (rightAngle : pointVectorDot rightVertex first second = 0) :
    quadrance (midpoint first second) first =
      quadrance (midpoint first second) rightVertex := by
  have fourNonzero : (4 : K) ≠ 0 := by
    have productNonzero :=
      RFAP.ExplicitField.mul_ne_zero twoNonzero twoNonzero
    simpa only [show (4 : K) = 2 * 2 by ring1] using productNonzero
  have pythagoras :
      quadrance first rightVertex + quadrance second rightVertex =
        quadrance first second := by
    apply sub_eq_zero.mp
    calc
      quadrance first rightVertex + quadrance second rightVertex -
          quadrance first second =
        2 * pointVectorDot rightVertex first second := by
          unfold quadrance pointVectorDot
          ring1
      _ = 0 := by rw [rightAngle]; ring1
  have endpointCleared :
      quadrance (midpoint first second) first * 4 =
        quadrance first second := by
    rw [midpoint_quadrance first second twoNonzero]
    exact RFAP.ExplicitField.div_mul_cancel _ fourNonzero
  have rightCleared := median_quadrance_cleared
    first second rightVertex twoNonzero
  apply eq_of_mul_eq_mul_right fourNonzero
  calc
    quadrance (midpoint first second) first * 4 =
        quadrance first second := endpointCleared
    _ = 2 * quadrance first rightVertex +
          2 * quadrance second rightVertex - quadrance first second := by
      rw [← pythagoras]
      ring1
    _ = quadrance (midpoint first second) rightVertex * 4 :=
      rightCleared.symm

/-- The altitude foot belonging to one vertex lies at the same nine-point
quadrance as the corresponding side midpoint. -/
theorem ninePoint_altitude_foot_quadrance
    [DecidableEq K]
    (vertex sideFirst sideSecond circumcenter orthocenter : Point K)
    (sideDistinct : sideFirst ≠ sideSecond)
    (twoNonzero : (2 : K) ≠ 0)
    (sideNonNull : ¬ (lineThrough sideFirst sideSecond sideDistinct).IsNull)
    (centerX : 2 * circumcenter.x + orthocenter.x =
      vertex.x + sideFirst.x + sideSecond.x)
    (centerY : 2 * circumcenter.y + orthocenter.y =
      vertex.y + sideFirst.y + sideSecond.y)
    (orthocenterOnAltitude :
      (altitudeThrough vertex
        (lineThrough sideFirst sideSecond sideDistinct)).Contains orthocenter) :
    let center := ninePointCenter circumcenter orthocenter
    let foot := altitudeFoot vertex
      (lineThrough sideFirst sideSecond sideDistinct) sideNonNull
    quadrance center foot = quadrance circumcenter vertex / 4 := by
  dsimp only
  let sideLine := lineThrough sideFirst sideSecond sideDistinct
  let sideMidpoint := midpoint sideFirst sideSecond
  let oppositeMidpoint := midpoint vertex orthocenter
  let center := ninePointCenter circumcenter orthocenter
  let foot := altitudeFoot vertex sideLine sideNonNull
  have pair := ninePoint_midpoint_pair vertex sideFirst sideSecond
    circumcenter orthocenter twoNonzero centerX centerY
  dsimp only at pair
  have sideMidpointOnLine : sideLine.Contains sideMidpoint :=
    line_contains_midpoint sideLine sideFirst sideSecond twoNonzero
      (lineThrough_contains_first sideFirst sideSecond sideDistinct)
      (lineThrough_contains_second sideFirst sideSecond sideDistinct)
  have footOnLine : sideLine.Contains foot := by
    exact altitudeFoot_on_line vertex sideLine sideNonNull
  have oppositeMidpointOnAltitude :
      (altitudeThrough vertex sideLine).Contains oppositeMidpoint :=
    line_contains_midpoint (altitudeThrough vertex sideLine) vertex
      orthocenter twoNonzero (altitudeThrough_contains vertex sideLine)
      orthocenterOnAltitude
  have footOnAltitude :
      (altitudeThrough vertex sideLine).Contains foot := by
    exact altitudeFoot_on_altitude vertex sideLine sideNonNull
  have rightAngle : pointVectorDot foot sideMidpoint oppositeMidpoint = 0 :=
    pointVectorDot_eq_zero_of_line_altitude sideLine vertex sideMidpoint
      oppositeMidpoint foot sideNonNull sideMidpointOnLine footOnLine
      oppositeMidpointOnAltitude footOnAltitude
  have rightQuadrance := midpoint_right_quadrance_of_dot_zero
    sideMidpoint oppositeMidpoint foot twoNonzero rightAngle
  rw [pair.1] at rightQuadrance
  exact rightQuadrance.symm.trans pair.2.1

/-- Theorem 117 (Nine point circle): for a non-null triangle, all three side
midpoints, all three altitude feet, and all three vertex--orthocenter
midpoints lie on one explicitly constructed circle. -/
theorem nine_point_circle
    [Nontrivial K] [DecidableEq K]
    (first second third : Point K)
    (firstSecondDistinct : first ≠ second)
    (firstThirdDistinct : first ≠ third)
    (secondThirdDistinct : second ≠ third)
    (notCollinear : ¬ Collinear first second third)
    (twoNonzero : (2 : K) ≠ 0)
    (firstSideNonNull :
      ¬ (lineThrough second third secondThirdDistinct).IsNull)
    (secondSideNonNull :
      ¬ (lineThrough first third firstThirdDistinct).IsNull)
    (thirdSideNonNull :
      ¬ (lineThrough first second firstSecondDistinct).IsNull) :
    let circumcenter :=
      circumcenterPoint first second third firstThirdDistinct
        secondThirdDistinct notCollinear
    let orthocenter :=
      orthocenterPoint first second third firstThirdDistinct
        secondThirdDistinct notCollinear
    let circleQuadrance := quadrance circumcenter first / 4
    let circle := ninePointCircle circumcenter orthocenter circleQuadrance
    circle.Contains (sideMidpointOppositeFirst first second third) ∧
      circle.Contains (sideMidpointOppositeSecond first second third) ∧
      circle.Contains (sideMidpointOppositeThird first second third) ∧
      circle.Contains (altitudeFoot first
        (lineThrough second third secondThirdDistinct) firstSideNonNull) ∧
      circle.Contains (altitudeFoot second
        (lineThrough first third firstThirdDistinct) secondSideNonNull) ∧
      circle.Contains (altitudeFoot third
        (lineThrough first second firstSecondDistinct) thirdSideNonNull) ∧
      circle.Contains (vertexOrthocenterMidpoint first orthocenter) ∧
      circle.Contains (vertexOrthocenterMidpoint second orthocenter) ∧
      circle.Contains (vertexOrthocenterMidpoint third orthocenter) := by
  dsimp only
  let circumcenter :=
    circumcenterPoint first second third firstThirdDistinct
      secondThirdDistinct notCollinear
  let orthocenter :=
    orthocenterPoint first second third firstThirdDistinct
      secondThirdDistinct notCollinear
  let center := ninePointCenter circumcenter orthocenter
  let circleQuadrance := quadrance circumcenter first / 4
  let circle := ninePointCircle circumcenter orthocenter circleQuadrance
  have clearedCenters := euler_center_cleared_coordinates first second third
    firstThirdDistinct secondThirdDistinct notCollinear twoNonzero
  have firstPair := ninePoint_midpoint_pair first second third circumcenter
    orthocenter twoNonzero clearedCenters.1 clearedCenters.2
  have secondCenterX : 2 * circumcenter.x + orthocenter.x =
      second.x + first.x + third.x := by
    rw [clearedCenters.1]
    ring1
  have secondCenterY : 2 * circumcenter.y + orthocenter.y =
      second.y + first.y + third.y := by
    rw [clearedCenters.2]
    ring1
  have secondPair := ninePoint_midpoint_pair second first third circumcenter
    orthocenter twoNonzero secondCenterX secondCenterY
  have thirdCenterX : 2 * circumcenter.x + orthocenter.x =
      third.x + first.x + second.x := by
    rw [clearedCenters.1]
    ring1
  have thirdCenterY : 2 * circumcenter.y + orthocenter.y =
      third.y + first.y + second.y := by
    rw [clearedCenters.2]
    ring1
  have thirdPair := ninePoint_midpoint_pair third first second circumcenter
    orthocenter twoNonzero thirdCenterX thirdCenterY
  dsimp only at firstPair secondPair thirdPair
  have centerFacts := DivineProportions.circumcenter first second third
    firstSecondDistinct firstThirdDistinct secondThirdDistinct notCollinear
    twoNonzero
  dsimp only at centerFacts
  have secondRadius : quadrance circumcenter second =
      quadrance circumcenter first := centerFacts.2.2.2.1.symm
  have thirdRadius : quadrance circumcenter third =
      quadrance circumcenter first :=
    centerFacts.2.2.2.2.symm.trans secondRadius
  have orthocenterFacts := DivineProportions.orthocenter first second third
    firstSecondDistinct firstThirdDistinct secondThirdDistinct notCollinear
  dsimp only at orthocenterFacts
  have firstFoot := ninePoint_altitude_foot_quadrance first second third
    circumcenter orthocenter secondThirdDistinct twoNonzero firstSideNonNull
    clearedCenters.1 clearedCenters.2 orthocenterFacts.1
  have secondFootRaw := ninePoint_altitude_foot_quadrance second first third
    circumcenter orthocenter firstThirdDistinct twoNonzero secondSideNonNull
    secondCenterX secondCenterY orthocenterFacts.2.1
  have secondFoot :
      quadrance center
          (altitudeFoot second (lineThrough first third firstThirdDistinct)
            secondSideNonNull) = circleQuadrance := by
    calc
      quadrance center
          (altitudeFoot second (lineThrough first third firstThirdDistinct)
            secondSideNonNull) = quadrance circumcenter second / 4 :=
        secondFootRaw
      _ = circleQuadrance := by rw [secondRadius]
  have thirdFootRaw := ninePoint_altitude_foot_quadrance third first second
    circumcenter orthocenter firstSecondDistinct twoNonzero thirdSideNonNull
    thirdCenterX thirdCenterY orthocenterFacts.2.2
  have thirdFoot :
      quadrance center
          (altitudeFoot third (lineThrough first second firstSecondDistinct)
            thirdSideNonNull) = circleQuadrance := by
    calc
      quadrance center
          (altitudeFoot third (lineThrough first second firstSecondDistinct)
            thirdSideNonNull) = quadrance circumcenter third / 4 :=
        thirdFootRaw
      _ = circleQuadrance := by rw [thirdRadius]
  have presentation := Conic.circleConic_isCirclePresentation
    center circleQuadrance
  have containsOfQuadrance := fun (point : Point K)
      (pointQuadrance : quadrance center point = circleQuadrance) =>
    (Conic.contains_iff_quadrance_eq circle center point circleQuadrance
      presentation).2 ((quadrance_symm point center).trans pointQuadrance)
  refine ⟨containsOfQuadrance _ firstPair.2.1,
    containsOfQuadrance _ (secondPair.2.1.trans (congrArg (fun value => value / 4)
      secondRadius)),
    containsOfQuadrance _ (thirdPair.2.1.trans (congrArg (fun value => value / 4)
      thirdRadius)),
    containsOfQuadrance _ firstFoot,
    containsOfQuadrance _ secondFoot,
    containsOfQuadrance _ thirdFoot,
    containsOfQuadrance _ firstPair.2.2,
    containsOfQuadrance _ (secondPair.2.2.trans (congrArg (fun value => value / 4)
      secondRadius)),
    containsOfQuadrance _ (thirdPair.2.2.trans (congrArg (fun value => value / 4)
      thirdRadius))⟩

/-- The midpoint of the side `A₁A₂` of a displayed quadrilateral. -/
def quadrilateralSideMidpoint12
    (first second _third _fourth : Point K) : Point K :=
  midpoint first second

/-- The midpoint of the side `A₂A₃` of a displayed quadrilateral. -/
def quadrilateralSideMidpoint23
    (_first second third _fourth : Point K) : Point K :=
  midpoint second third

/-- The midpoint of the side `A₃A₄` of a displayed quadrilateral. -/
def quadrilateralSideMidpoint34
    (_first _second third fourth : Point K) : Point K :=
  midpoint third fourth

/-- The midpoint of the side `A₁A₄` of a displayed quadrilateral. -/
def quadrilateralSideMidpoint14
    (first _second _third fourth : Point K) : Point K :=
  midpoint first fourth

/-- The center used for Exercise 18.3's eight-point circle. -/
def eightPointCenter (first second third fourth : Point K) : Point K :=
  midpoint (quadrilateralSideMidpoint12 first second third fourth)
    (quadrilateralSideMidpoint34 first second third fourth)

/-- The explicit circle used for Exercise 18.3. -/
def eightPointCircle [Nontrivial K]
    (first second third fourth : Point K) : Conic K :=
  let center := eightPointCenter first second third fourth
  Conic.circleConic center
    (quadrance center
      (quadrilateralSideMidpoint12 first second third fourth))

/-- The two pairs of opposite side midpoints of any quadrilateral have the
same midpoint.  This is the finite coordinate form of the parallelogram-center
observation behind the eight-point circle. -/
theorem quadrilateral_opposite_midpoint_centers_eq
    (first second third fourth : Point K) :
    midpoint (quadrilateralSideMidpoint12 first second third fourth)
        (quadrilateralSideMidpoint34 first second third fourth) =
      midpoint (quadrilateralSideMidpoint23 first second third fourth)
        (quadrilateralSideMidpoint14 first second third fourth) := by
  apply Point.ext
  · simp only [quadrilateralSideMidpoint12, quadrilateralSideMidpoint23,
      quadrilateralSideMidpoint34, quadrilateralSideMidpoint14, midpoint,
      RFAP.ExplicitField.div_eq_mul_inv]
    ring1
  · simp only [quadrilateralSideMidpoint12, quadrilateralSideMidpoint23,
      quadrilateralSideMidpoint34, quadrilateralSideMidpoint14, midpoint,
      RFAP.ExplicitField.div_eq_mul_inv]
    ring1

/-- Perpendicular diagonals make the corner at `M₁₂` of the midpoint
parallelogram right.  No division is cancelled in this calculation. -/
theorem quadrilateral_midpoint_right_angle
    [DecidableEq K]
    (first second third fourth : Point K)
    (firstThirdDistinct : first ≠ third)
    (secondFourthDistinct : second ≠ fourth)
    (diagonalsPerpendicular :
      (lineThrough first third firstThirdDistinct).Perpendicular
        (lineThrough second fourth secondFourthDistinct)) :
    pointVectorDot
        (quadrilateralSideMidpoint12 first second third fourth)
        (quadrilateralSideMidpoint23 first second third fourth)
        (quadrilateralSideMidpoint14 first second third fourth) = 0 := by
  unfold Line.Perpendicular lineThrough at diagonalsPerpendicular
  simp only [quadrilateralSideMidpoint12, quadrilateralSideMidpoint23,
    quadrilateralSideMidpoint14, pointVectorDot, midpoint,
    RFAP.ExplicitField.div_eq_mul_inv]
  calc
    (((second.x + third.x) * (2 : K)⁻¹ -
            (first.x + second.x) * (2 : K)⁻¹) *
          ((first.x + fourth.x) * (2 : K)⁻¹ -
            (first.x + second.x) * (2 : K)⁻¹) +
        ((second.y + third.y) * (2 : K)⁻¹ -
            (first.y + second.y) * (2 : K)⁻¹) *
          ((first.y + fourth.y) * (2 : K)⁻¹ -
            (first.y + second.y) * (2 : K)⁻¹)) =
      ((first.y - third.y) * (second.y - fourth.y) +
          (third.x - first.x) * (fourth.x - second.x)) *
        ((2 : K)⁻¹ * (2 : K)⁻¹) := by ring1
    _ = 0 := by rw [diagonalsPerpendicular]; ring1

/-- An altitude foot from one endpoint of a diameter has the same quadrance
from the diameter midpoint as that endpoint.  The other endpoint is supplied
as the midpoint of a non-null target side. -/
theorem altitudeFoot_diameter_quadrance
    [DecidableEq K]
    (source sideFirst sideSecond : Point K)
    (sideDistinct : sideFirst ≠ sideSecond)
    (twoNonzero : (2 : K) ≠ 0)
    (sideNonNull :
      ¬ (lineThrough sideFirst sideSecond sideDistinct).IsNull) :
    let oppositeSideMidpoint := midpoint sideFirst sideSecond
    let center := midpoint source oppositeSideMidpoint
    let foot := altitudeFoot source
      (lineThrough sideFirst sideSecond sideDistinct) sideNonNull
    quadrance center foot = quadrance center source := by
  dsimp only
  let sideLine := lineThrough sideFirst sideSecond sideDistinct
  let oppositeSideMidpoint := midpoint sideFirst sideSecond
  let center := midpoint source oppositeSideMidpoint
  let foot := altitudeFoot source sideLine sideNonNull
  have midpointOnLine : sideLine.Contains oppositeSideMidpoint :=
    line_contains_midpoint sideLine sideFirst sideSecond twoNonzero
      (lineThrough_contains_first sideFirst sideSecond sideDistinct)
      (lineThrough_contains_second sideFirst sideSecond sideDistinct)
  have footOnLine : sideLine.Contains foot :=
    altitudeFoot_on_line source sideLine sideNonNull
  have sourceOnAltitude :
      (altitudeThrough source sideLine).Contains source :=
    altitudeThrough_contains source sideLine
  have footOnAltitude :
      (altitudeThrough source sideLine).Contains foot :=
    altitudeFoot_on_altitude source sideLine sideNonNull
  have rightAngle :
      pointVectorDot foot oppositeSideMidpoint source = 0 :=
    pointVectorDot_eq_zero_of_line_altitude sideLine source
      oppositeSideMidpoint source foot sideNonNull midpointOnLine footOnLine
      sourceOnAltitude footOnAltitude
  have rightQuadrance := midpoint_right_quadrance_of_dot_zero
    oppositeSideMidpoint source foot twoNonzero rightAngle
  have midpointOrder :
      midpoint oppositeSideMidpoint source = center := by
    exact midpoint_symm oppositeSideMidpoint source
  rw [midpointOrder] at rightQuadrance
  have endpointQuadrance := midpoint_equal_quadrance source
    oppositeSideMidpoint twoNonzero
  exact rightQuadrance.symm.trans endpointQuadrance.symm

/-- Exercise 18.3 (Eight point circle): if the two displayed diagonals are
perpendicular and all four target sides are non-null, the four side midpoints
and the four altitude feet from them to the opposite sides lie on one
explicitly constructed circle. -/
theorem exercise_18_3
    [Nontrivial K] [DecidableEq K]
    (first second third fourth : Point K)
    (firstSecondDistinct : first ≠ second)
    (secondThirdDistinct : second ≠ third)
    (thirdFourthDistinct : third ≠ fourth)
    (firstFourthDistinct : first ≠ fourth)
    (firstThirdDistinct : first ≠ third)
    (secondFourthDistinct : second ≠ fourth)
    (twoNonzero : (2 : K) ≠ 0)
    (diagonalsPerpendicular :
      (lineThrough first third firstThirdDistinct).Perpendicular
        (lineThrough second fourth secondFourthDistinct))
    (firstSideNonNull :
      ¬ (lineThrough first second firstSecondDistinct).IsNull)
    (secondSideNonNull :
      ¬ (lineThrough second third secondThirdDistinct).IsNull)
    (thirdSideNonNull :
      ¬ (lineThrough third fourth thirdFourthDistinct).IsNull)
    (fourthSideNonNull :
      ¬ (lineThrough first fourth firstFourthDistinct).IsNull) :
    let midpoint12 := quadrilateralSideMidpoint12 first second third fourth
    let midpoint23 := quadrilateralSideMidpoint23 first second third fourth
    let midpoint34 := quadrilateralSideMidpoint34 first second third fourth
    let midpoint14 := quadrilateralSideMidpoint14 first second third fourth
    let circle := eightPointCircle first second third fourth
    circle.Contains midpoint12 ∧
      circle.Contains midpoint23 ∧
      circle.Contains midpoint34 ∧
      circle.Contains midpoint14 ∧
      circle.Contains (altitudeFoot midpoint12
        (lineThrough third fourth thirdFourthDistinct) thirdSideNonNull) ∧
      circle.Contains (altitudeFoot midpoint23
        (lineThrough first fourth firstFourthDistinct) fourthSideNonNull) ∧
      circle.Contains (altitudeFoot midpoint34
        (lineThrough first second firstSecondDistinct) firstSideNonNull) ∧
      circle.Contains (altitudeFoot midpoint14
        (lineThrough second third secondThirdDistinct) secondSideNonNull) := by
  dsimp only
  let midpoint12 := quadrilateralSideMidpoint12 first second third fourth
  let midpoint23 := quadrilateralSideMidpoint23 first second third fourth
  let midpoint34 := quadrilateralSideMidpoint34 first second third fourth
  let midpoint14 := quadrilateralSideMidpoint14 first second third fourth
  let center := eightPointCenter first second third fourth
  let radius := quadrance center midpoint12
  let circle := eightPointCircle first second third fourth
  have centersEqual : center = midpoint midpoint23 midpoint14 := by
    exact quadrilateral_opposite_midpoint_centers_eq first second third fourth
  have midpoint34Quadrance :
      quadrance center midpoint34 = radius := by
    exact (midpoint_equal_quadrance midpoint12 midpoint34 twoNonzero).symm
  have rightAngle : pointVectorDot midpoint12 midpoint23 midpoint14 = 0 :=
    quadrilateral_midpoint_right_angle first second third fourth
      firstThirdDistinct secondFourthDistinct diagonalsPerpendicular
  have midpoint23QuadranceRaw := midpoint_right_quadrance_of_dot_zero
    midpoint23 midpoint14 midpoint12 twoNonzero rightAngle
  rw [← centersEqual] at midpoint23QuadranceRaw
  have midpoint23Quadrance : quadrance center midpoint23 = radius :=
    midpoint23QuadranceRaw
  have midpoint14Pair := midpoint_equal_quadrance midpoint23 midpoint14
    twoNonzero
  rw [← centersEqual] at midpoint14Pair
  have midpoint14Quadrance : quadrance center midpoint14 = radius :=
    midpoint14Pair.symm.trans midpoint23Quadrance
  have foot12Quadrance :
      quadrance center
          (altitudeFoot midpoint12
            (lineThrough third fourth thirdFourthDistinct)
            thirdSideNonNull) = radius :=
    altitudeFoot_diameter_quadrance midpoint12 third fourth
      thirdFourthDistinct twoNonzero thirdSideNonNull
  have foot23Raw :
      quadrance (midpoint midpoint23 midpoint14)
          (altitudeFoot midpoint23
            (lineThrough first fourth firstFourthDistinct)
            fourthSideNonNull) =
        quadrance (midpoint midpoint23 midpoint14) midpoint23 :=
    altitudeFoot_diameter_quadrance midpoint23 first fourth
      firstFourthDistinct twoNonzero fourthSideNonNull
  have foot23Quadrance :
      quadrance center
          (altitudeFoot midpoint23
            (lineThrough first fourth firstFourthDistinct)
            fourthSideNonNull) = radius := by
    rw [← centersEqual] at foot23Raw
    exact foot23Raw.trans midpoint23Quadrance
  have foot34Raw :
      quadrance (midpoint midpoint34 midpoint12)
          (altitudeFoot midpoint34
            (lineThrough first second firstSecondDistinct)
            firstSideNonNull) =
        quadrance (midpoint midpoint34 midpoint12) midpoint34 :=
    altitudeFoot_diameter_quadrance midpoint34 first second
      firstSecondDistinct twoNonzero firstSideNonNull
  have foot34Quadrance :
      quadrance center
          (altitudeFoot midpoint34
            (lineThrough first second firstSecondDistinct)
            firstSideNonNull) = radius := by
    rw [midpoint_symm midpoint34 midpoint12] at foot34Raw
    exact foot34Raw.trans midpoint34Quadrance
  have foot14Raw :
      quadrance (midpoint midpoint14 midpoint23)
          (altitudeFoot midpoint14
            (lineThrough second third secondThirdDistinct)
            secondSideNonNull) =
        quadrance (midpoint midpoint14 midpoint23) midpoint14 :=
    altitudeFoot_diameter_quadrance midpoint14 second third
      secondThirdDistinct twoNonzero secondSideNonNull
  have foot14Quadrance :
      quadrance center
          (altitudeFoot midpoint14
            (lineThrough second third secondThirdDistinct)
            secondSideNonNull) = radius := by
    rw [midpoint_symm midpoint14 midpoint23, ← centersEqual] at foot14Raw
    exact foot14Raw.trans midpoint14Quadrance
  have presentation := Conic.circleConic_isCirclePresentation center radius
  have containsOfQuadrance := fun (point : Point K)
      (pointQuadrance : quadrance center point = radius) =>
    (Conic.contains_iff_quadrance_eq circle center point radius
      presentation).2 ((quadrance_symm point center).trans pointQuadrance)
  exact ⟨containsOfQuadrance midpoint12 rfl,
    containsOfQuadrance midpoint23 midpoint23Quadrance,
    containsOfQuadrance midpoint34 midpoint34Quadrance,
    containsOfQuadrance midpoint14 midpoint14Quadrance,
    containsOfQuadrance _ foot12Quadrance,
    containsOfQuadrance _ foot23Quadrance,
    containsOfQuadrance _ foot34Quadrance,
    containsOfQuadrance _ foot14Quadrance⟩

end DivineProportions
