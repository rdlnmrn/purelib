import mathlib.Tactic.QuotientFreeRing
import DivineProportions.Stars.OrderSeven
import DivineProportions.Triangles.Isosceles

/-!
# Divine Proportions, Theorem 98: polygon corner triangles

The source construction uses only three successive polygon vertices and the
three finite reflections relating them.  `PolygonTriangleConfiguration`
stores precisely that finite window; no polygon indexed by all integers is
introduced.
-/

namespace DivineProportions

variable {K : Type*} [RFAP.ExplicitField K]

private theorem eq_of_mul_eq_mul_right
    {left right factor : K} (factorNonzero : factor ≠ 0)
    (productsEqual : left * factor = right * factor) : left = right := by
  have factorCancel : factor * factor⁻¹ = (1 : K) :=
    RFAP.ExplicitField.mul_inv_cancel factor factorNonzero
  calc
    left = left * 1 := by rw [mul_one]
    _ = left * (factor * factor⁻¹) := by rw [factorCancel]
    _ = (left * factor) * factor⁻¹ := by ring1
    _ = (right * factor) * factor⁻¹ := by rw [productsEqual]
    _ = right * (factor * factor⁻¹) := by ring1
    _ = right := by rw [factorCancel, mul_one]

private theorem eq_of_mul_eq_mul_left
    {left right factor : K} (factorNonzero : factor ≠ 0)
    (productsEqual : factor * left = factor * right) : left = right := by
  apply eq_of_mul_eq_mul_right factorNonzero
  calc
    left * factor = factor * left := by ring1
    _ = factor * right := productsEqual
    _ = right * factor := by ring1

/-- The perpendicular quadrance from `point` to a mirror through `center` is
the radial quadrance multiplied by the spread between the radius and mirror.
This is the geometric ratio used in the source proof of Isosceles reflection. -/
theorem pointLineQuadrance_eq_spread_mul_quadrance [DecidableEq K]
    (center point : Point K) (distinct : center ≠ point)
    (radialNonNull : ¬ (lineThrough center point distinct).IsNull)
    (mirror : Line K) (mirrorNonNull : ¬ mirror.IsNull)
    (centerOnMirror : mirror.Contains center) :
    pointLineQuadrance point mirror mirrorNonNull =
      spread (lineThrough center point distinct) mirror
          radialNonNull mirrorNonNull * quadrance center point := by
  have radialQuadranceNonzero : quadrance center point ≠ 0 := by
    rw [← lineThrough_norm_eq_quadrance center point distinct]
    exact radialNonNull
  have mirrorNormNonzero : lineNorm mirror ≠ 0 := mirrorNonNull
  have denominatorNonzero :
      quadrance center point * lineNorm mirror ≠ 0 :=
    RFAP.ExplicitField.mul_ne_zero radialQuadranceNonzero mirrorNormNonzero
  have determinantNegated :
      (lineThrough center point distinct).a * mirror.b -
          mirror.a * (lineThrough center point distinct).b =
        -(mirror.a * point.x + mirror.b * point.y + mirror.c) := by
    unfold Line.Contains at centerOnMirror
    simp only [lineThrough_a, lineThrough_b]
    calc
      (center.y - point.y) * mirror.b -
          mirror.a * (point.x - center.x) =
        (mirror.a * center.x + mirror.b * center.y + mirror.c) -
          (mirror.a * point.x + mirror.b * point.y + mirror.c) := by ring1
      _ = -(mirror.a * point.x + mirror.b * point.y + mirror.c) := by
        rw [centerOnMirror]
        ring1
  have determinantSquare :
      ((lineThrough center point distinct).a * mirror.b -
          mirror.a * (lineThrough center point distinct).b) ^ 2 =
        (mirror.a * point.x + mirror.b * point.y + mirror.c) ^ 2 := by
    rw [determinantNegated]
    ring1
  rw [pointLineQuadrance_formula]
  unfold spread
  rw [lineThrough_norm_eq_quadrance center point distinct,
    determinantSquare]
  apply eq_of_mul_eq_mul_right mirrorNormNonzero
  calc
    ((mirror.a * point.x + mirror.b * point.y + mirror.c) ^ 2 /
          lineNorm mirror) * lineNorm mirror =
        (mirror.a * point.x + mirror.b * point.y + mirror.c) ^ 2 :=
      RFAP.ExplicitField.div_mul_cancel _ mirrorNormNonzero
    _ = ((mirror.a * point.x + mirror.b * point.y + mirror.c) ^ 2 /
          (quadrance center point * lineNorm mirror)) *
            (quadrance center point * lineNorm mirror) :=
      (RFAP.ExplicitField.div_mul_cancel _ denominatorNonzero).symm
    _ = ((mirror.a * point.x + mirror.b * point.y + mirror.c) ^ 2 /
          (quadrance center point * lineNorm mirror) *
            quadrance center point) * lineNorm mirror := by ring1

/-- A reflection chord has four times the point-to-mirror quadrance. -/
theorem reflectPoint_chord_quadrance
    (mirror : Line K) (mirrorNonNull : ¬ mirror.IsNull) (point : Point K) :
    quadrance point (reflectPoint mirror mirrorNonNull point) =
      4 * pointLineQuadrance point mirror mirrorNonNull := by
  unfold reflectPoint pointLineQuadrance rotateInPoint quadrance
  ring1

/-- Geometric form of the Isosceles reflection theorem used by Theorem 98. -/
theorem reflectPoint_chord_quadrance_eq_spread [DecidableEq K]
    (center point : Point K) (distinct : center ≠ point)
    (radialNonNull : ¬ (lineThrough center point distinct).IsNull)
    (mirror : Line K) (mirrorNonNull : ¬ mirror.IsNull)
    (centerOnMirror : mirror.Contains center) :
    quadrance point (reflectPoint mirror mirrorNonNull point) =
      4 * spread (lineThrough center point distinct) mirror
        radialNonNull mirrorNonNull * quadrance center point := by
  rw [reflectPoint_chord_quadrance,
    pointLineQuadrance_eq_spread_mul_quadrance center point distinct
      radialNonNull mirror mirrorNonNull centerOnMirror]
  ring1

/-- The finite scalar calculation at the heart of Theorem 98.  The reflection
part of the geometric theorem supplies the two quadrance formulas, while the
ordinary Spread law and Equal spreads theorem supply the three spread inputs. -/
theorem polygon_triangle_scalars
    (q r d value baseFirst apex baseThird : K)
    (qNonzero : q ≠ 0) (rNonzero : r ≠ 0) (dNonzero : d ≠ 0)
    (valueNonzero : value ≠ 0) (baseFirstNonzero : baseFirst ≠ 0)
    (apexNonzero : apex ≠ 0) (twoNonzero : (2 : K) ≠ 0)
    (sideValue : r = 4 * value * q)
    (diagonalValue : d = 16 * value * (1 - value) * q)
    (firstSpreadLaw : baseFirst / r = apex / d)
    (secondSpreadLaw : apex / d = baseThird / r)
    (equalSpreadAlternatives :
      apex = 0 ∨ apex = 4 * baseFirst * (1 - baseFirst)) :
    r = 4 * value * q ∧
      d = 16 * value * (1 - value) * q ∧
      baseFirst = value ∧ baseThird = value ∧
      apex = 4 * value * (1 - value) := by
  have baseSpreadsEqual : baseFirst = baseThird := by
    calc
      baseFirst = (baseFirst / r) * r :=
        (RFAP.ExplicitField.div_mul_cancel baseFirst rNonzero).symm
      _ = (baseThird / r) * r := by rw [firstSpreadLaw, secondSpreadLaw]
      _ = baseThird := RFAP.ExplicitField.div_mul_cancel baseThird rNonzero
  have apexLogistic : apex = 4 * baseFirst * (1 - baseFirst) := by
    rcases equalSpreadAlternatives with apexZero | logistic
    · exact False.elim (apexNonzero apexZero)
    · exact logistic
  have diagonalFromBase :=
    (isosceles_triangle r d baseFirst apex rNonzero dNonzero
      baseFirstNonzero twoNonzero firstSpreadLaw apexLogistic).1
  have fourNonzero : (4 : K) ≠ 0 := by
    have fourAsProduct : (4 : K) = 2 * 2 := by ring1
    rw [fourAsProduct]
    exact RFAP.ExplicitField.mul_ne_zero twoNonzero twoNonzero
  have sixteenNonzero : (16 : K) ≠ 0 := by
    have sixteenAsProduct : (16 : K) = 4 * 4 := by ring1
    rw [sixteenAsProduct]
    exact RFAP.ExplicitField.mul_ne_zero fourNonzero fourNonzero
  have cancellationNonzero : (16 : K) * value * q ≠ 0 :=
    RFAP.ExplicitField.mul_ne_zero
      (RFAP.ExplicitField.mul_ne_zero sixteenNonzero valueNonzero) qNonzero
  have complementsEqual : 1 - baseFirst = 1 - value := by
    apply eq_of_mul_eq_mul_left cancellationNonzero
    calc
      (16 * value * q) * (1 - baseFirst) = d := by
        rw [diagonalFromBase, sideValue]
        ring1
      _ = (16 * value * q) * (1 - value) := by
        rw [diagonalValue]
        ring1
  have baseFirstValue : baseFirst = value := by
    calc
      baseFirst = 1 - (1 - baseFirst) := by ring1
      _ = 1 - (1 - value) := by rw [complementsEqual]
      _ = value := by ring1
  exact ⟨sideValue, diagonalValue, baseFirstValue,
    baseSpreadsEqual.symm.trans baseFirstValue, by
      rw [apexLogistic, baseFirstValue]⟩

/-- Reversing the endpoints only reverses both displayed direction
coefficients, so the two line representatives are parallel. -/
private theorem lineThrough_reverse_parallel [DecidableEq K]
    (first second : Point K) (distinct : first ≠ second) :
    (lineThrough first second distinct).Parallel
      (lineThrough second first distinct.symm) := by
  unfold Line.Parallel lineThrough
  ring1

private theorem lineThrough_reverse_nonNull [DecidableEq K]
    (first second : Point K) (distinct : first ≠ second)
    (forwardNonNull : ¬ (lineThrough first second distinct).IsNull) :
    ¬ (lineThrough second first distinct.symm).IsNull := by
  intro reverseNull
  apply forwardNonNull
  change lineNorm (lineThrough first second distinct) = 0
  change lineNorm (lineThrough second first distinct.symm) = 0 at reverseNull
  rw [lineThrough_norm_eq_quadrance first second distinct,
    quadrance_symm first second,
    ← lineThrough_norm_eq_quadrance second first distinct.symm]
  exact reverseNull

private theorem quadrance_ne_zero_of_line_nonNull [DecidableEq K]
    (first second : Point K) (distinct : first ≠ second)
    (lineNonNull : ¬ (lineThrough first second distinct).IsNull) :
    quadrance first second ≠ 0 := by
  intro quadranceZero
  apply lineNonNull
  exact (null_line_iff_quadrance_zero first second distinct).2 quadranceZero

/-- The finite three-vertex window used in the proof of Theorem 98.
`second` is the reflection of `first` in the first intervening star line;
`third` is obtained by the next reflection, and also by reflecting `first`
in the middle radial line. -/
structure PolygonTriangleConfiguration (K : Type*) [RFAP.ExplicitField K]
    [DecidableEq K] (value : K) where
  center : Point K
  first : Point K
  second : Point K
  third : Point K
  centerFirstDistinct : center ≠ first
  centerSecondDistinct : center ≠ second
  centerThirdDistinct : center ≠ third
  firstSecondDistinct : first ≠ second
  firstThirdDistinct : first ≠ third
  secondThirdDistinct : second ≠ third
  centerFirstNonNull :
    ¬ (lineThrough center first centerFirstDistinct).IsNull
  centerSecondNonNull :
    ¬ (lineThrough center second centerSecondDistinct).IsNull
  centerThirdNonNull :
    ¬ (lineThrough center third centerThirdDistinct).IsNull
  firstSecondNonNull :
    ¬ (lineThrough first second firstSecondDistinct).IsNull
  firstThirdNonNull :
    ¬ (lineThrough first third firstThirdDistinct).IsNull
  secondThirdNonNull :
    ¬ (lineThrough second third secondThirdDistinct).IsNull
  firstMirror : Line K
  secondMirror : Line K
  firstMirrorNonNull : ¬ firstMirror.IsNull
  secondMirrorNonNull : ¬ secondMirror.IsNull
  centerOnFirstMirror : firstMirror.Contains center
  centerOnSecondMirror : secondMirror.Contains center
  secondReflection :
    second = reflectPoint firstMirror firstMirrorNonNull first
  thirdReflection :
    third = reflectPoint secondMirror secondMirrorNonNull second
  diagonalReflection :
    third = reflectPoint
      (lineThrough center second centerSecondDistinct)
      centerSecondNonNull first
  firstMirrorSpread :
    spread (lineThrough center first centerFirstDistinct) firstMirror
      centerFirstNonNull firstMirrorNonNull = value
  secondMirrorSpread :
    spread (lineThrough center second centerSecondDistinct) secondMirror
      centerSecondNonNull secondMirrorNonNull = value
  doubleRadialSpread :
    spread (lineThrough center first centerFirstDistinct)
        (lineThrough center second centerSecondDistinct)
        centerFirstNonNull centerSecondNonNull =
      4 * value * (1 - value)
  secondRadius : quadrance center second = quadrance center first
  thirdRadius : quadrance center third = quadrance center first
  firstCornerNonparallel :
    ¬ (lineThrough first second firstSecondDistinct).Parallel
      (lineThrough first third firstThirdDistinct)
  middleCornerNonparallel :
    ¬ (lineThrough first second firstSecondDistinct).Parallel
      (lineThrough second third secondThirdDistinct)

/-- Theorem 98 (Polygon triangle): the two successive sides have quadrance
`4sQ`, the short diagonal has quadrance `16s(1-s)Q`, the two base spreads are
`s`, and the remaining spread is `4s(1-s)`. -/
theorem polygon_triangle [Nontrivial K] [DecidableEq K]
    (value : K) (valueNonzero : value ≠ 0)
    (twoNonzero : (2 : K) ≠ 0)
    (configuration : PolygonTriangleConfiguration K value) :
    quadrance configuration.first configuration.second =
        4 * value * quadrance configuration.center configuration.first ∧
      quadrance configuration.second configuration.third =
        4 * value * quadrance configuration.center configuration.first ∧
      quadrance configuration.first configuration.third =
        16 * value * (1 - value) *
          quadrance configuration.center configuration.first ∧
      spread
          (lineThrough configuration.first configuration.second
            configuration.firstSecondDistinct)
          (lineThrough configuration.first configuration.third
            configuration.firstThirdDistinct)
          configuration.firstSecondNonNull
          configuration.firstThirdNonNull = value ∧
      spread
          (lineThrough configuration.first configuration.third
            configuration.firstThirdDistinct)
          (lineThrough configuration.second configuration.third
            configuration.secondThirdDistinct)
          configuration.firstThirdNonNull
          configuration.secondThirdNonNull = value ∧
      spread
          (lineThrough configuration.first configuration.second
            configuration.firstSecondDistinct)
          (lineThrough configuration.second configuration.third
            configuration.secondThirdDistinct)
          configuration.firstSecondNonNull
          configuration.secondThirdNonNull =
        4 * value * (1 - value) := by
  let q := quadrance configuration.center configuration.first
  let r := quadrance configuration.first configuration.second
  let d := quadrance configuration.first configuration.third
  let firstSide := lineThrough configuration.first configuration.second
    configuration.firstSecondDistinct
  let diagonal := lineThrough configuration.first configuration.third
    configuration.firstThirdDistinct
  let secondSide := lineThrough configuration.second configuration.third
    configuration.secondThirdDistinct
  let baseFirst := spread firstSide diagonal
    configuration.firstSecondNonNull configuration.firstThirdNonNull
  let apex := spread firstSide secondSide
    configuration.firstSecondNonNull configuration.secondThirdNonNull
  let baseThird := spread diagonal secondSide
    configuration.firstThirdNonNull configuration.secondThirdNonNull
  have qNonzero : q ≠ 0 := by
    unfold q
    exact quadrance_ne_zero_of_line_nonNull configuration.center
      configuration.first configuration.centerFirstDistinct
      configuration.centerFirstNonNull
  have rNonzero : r ≠ 0 := by
    unfold r
    exact quadrance_ne_zero_of_line_nonNull configuration.first
      configuration.second configuration.firstSecondDistinct
      configuration.firstSecondNonNull
  have dNonzero : d ≠ 0 := by
    unfold d
    exact quadrance_ne_zero_of_line_nonNull configuration.first
      configuration.third configuration.firstThirdDistinct
      configuration.firstThirdNonNull
  have baseFirstNonzero : baseFirst ≠ 0 := by
    intro spreadZero
    apply configuration.firstCornerNonparallel
    exact (spread_eq_zero_iff_parallel firstSide diagonal
      configuration.firstSecondNonNull
      configuration.firstThirdNonNull).1 spreadZero
  have apexNonzero : apex ≠ 0 := by
    intro spreadZero
    apply configuration.middleCornerNonparallel
    exact (spread_eq_zero_iff_parallel firstSide secondSide
      configuration.firstSecondNonNull
      configuration.secondThirdNonNull).1 spreadZero
  have firstSideValue : r = 4 * value * q := by
    unfold r q
    calc
      quadrance configuration.first configuration.second =
          quadrance configuration.first
            (reflectPoint configuration.firstMirror
              configuration.firstMirrorNonNull configuration.first) := by
        rw [configuration.secondReflection]
      _ = 4 * spread
            (lineThrough configuration.center configuration.first
              configuration.centerFirstDistinct)
            configuration.firstMirror configuration.centerFirstNonNull
            configuration.firstMirrorNonNull *
          quadrance configuration.center configuration.first :=
        reflectPoint_chord_quadrance_eq_spread configuration.center
          configuration.first configuration.centerFirstDistinct
          configuration.centerFirstNonNull configuration.firstMirror
          configuration.firstMirrorNonNull configuration.centerOnFirstMirror
      _ = 4 * value *
          quadrance configuration.center configuration.first := by
        rw [configuration.firstMirrorSpread]
  have secondSideValue :
      quadrance configuration.second configuration.third = 4 * value * q := by
    unfold q
    calc
      quadrance configuration.second configuration.third =
          quadrance configuration.second
            (reflectPoint configuration.secondMirror
              configuration.secondMirrorNonNull configuration.second) := by
        rw [configuration.thirdReflection]
      _ = 4 * spread
            (lineThrough configuration.center configuration.second
              configuration.centerSecondDistinct)
            configuration.secondMirror configuration.centerSecondNonNull
            configuration.secondMirrorNonNull *
          quadrance configuration.center configuration.second :=
        reflectPoint_chord_quadrance_eq_spread configuration.center
          configuration.second configuration.centerSecondDistinct
          configuration.centerSecondNonNull configuration.secondMirror
          configuration.secondMirrorNonNull configuration.centerOnSecondMirror
      _ = 4 * value * quadrance configuration.center configuration.first := by
        rw [configuration.secondMirrorSpread, configuration.secondRadius]
  have diagonalValue : d = 16 * value * (1 - value) * q := by
    unfold d q
    calc
      quadrance configuration.first configuration.third =
          quadrance configuration.first
            (reflectPoint
              (lineThrough configuration.center configuration.second
                configuration.centerSecondDistinct)
              configuration.centerSecondNonNull configuration.first) := by
        rw [configuration.diagonalReflection]
      _ = 4 * spread
            (lineThrough configuration.center configuration.first
              configuration.centerFirstDistinct)
            (lineThrough configuration.center configuration.second
              configuration.centerSecondDistinct)
            configuration.centerFirstNonNull
            configuration.centerSecondNonNull *
          quadrance configuration.center configuration.first :=
        reflectPoint_chord_quadrance_eq_spread configuration.center
          configuration.first configuration.centerFirstDistinct
          configuration.centerFirstNonNull
          (lineThrough configuration.center configuration.second
            configuration.centerSecondDistinct)
          configuration.centerSecondNonNull
          (lineThrough_contains_first configuration.center configuration.second
            configuration.centerSecondDistinct)
      _ = 16 * value * (1 - value) *
          quadrance configuration.center configuration.first := by
        rw [configuration.doubleRadialSpread]
        ring1
  have sideQuadrancesEqual :
      quadrance configuration.second configuration.third = r := by
    calc
      quadrance configuration.second configuration.third = 4 * value * q :=
        secondSideValue
      _ = r := firstSideValue.symm
  let reversedFirstSideNonNull := lineThrough_reverse_nonNull
    configuration.first configuration.second
    configuration.firstSecondDistinct configuration.firstSecondNonNull
  let reversedDiagonalNonNull := lineThrough_reverse_nonNull
    configuration.first configuration.third configuration.firstThirdDistinct
    configuration.firstThirdNonNull
  let reversedSecondSideNonNull := lineThrough_reverse_nonNull
    configuration.second configuration.third
    configuration.secondThirdDistinct configuration.secondThirdNonNull
  have apexCanonical :
      spread
          (lineThrough configuration.second configuration.first
            configuration.firstSecondDistinct.symm)
          secondSide reversedFirstSideNonNull
          configuration.secondThirdNonNull = apex := by
    unfold apex firstSide
    exact spread_eq_of_parallel_pairs
      (lineThrough configuration.second configuration.first
        configuration.firstSecondDistinct.symm)
      secondSide
      (lineThrough configuration.first configuration.second
        configuration.firstSecondDistinct)
      secondSide reversedFirstSideNonNull configuration.secondThirdNonNull
      configuration.firstSecondNonNull configuration.secondThirdNonNull
      (Line.parallel_symm (lineThrough_reverse_parallel
        configuration.first configuration.second
        configuration.firstSecondDistinct))
      (Line.parallel_refl secondSide)
  have baseThirdCanonical :
      spread
          (lineThrough configuration.third configuration.first
            configuration.firstThirdDistinct.symm)
          (lineThrough configuration.third configuration.second
            configuration.secondThirdDistinct.symm)
          reversedDiagonalNonNull reversedSecondSideNonNull = baseThird := by
    unfold baseThird diagonal secondSide
    exact spread_eq_of_parallel_pairs
      (lineThrough configuration.third configuration.first
        configuration.firstThirdDistinct.symm)
      (lineThrough configuration.third configuration.second
        configuration.secondThirdDistinct.symm)
      (lineThrough configuration.first configuration.third
        configuration.firstThirdDistinct)
      (lineThrough configuration.second configuration.third
        configuration.secondThirdDistinct)
      reversedDiagonalNonNull reversedSecondSideNonNull
      configuration.firstThirdNonNull configuration.secondThirdNonNull
      (Line.parallel_symm (lineThrough_reverse_parallel
        configuration.first configuration.third
        configuration.firstThirdDistinct))
      (Line.parallel_symm (lineThrough_reverse_parallel
        configuration.second configuration.third
        configuration.secondThirdDistinct))
  have spreadLaws := spread_law configuration.first configuration.second
    configuration.third configuration.firstSecondDistinct
    configuration.firstThirdDistinct configuration.secondThirdDistinct
    configuration.firstSecondNonNull configuration.firstThirdNonNull
    configuration.secondThirdNonNull twoNonzero
  have firstSpreadLaw : baseFirst / r = apex / d := by
    have law := spreadLaws.1
    rw [sideQuadrancesEqual] at law
    change baseFirst / r =
      spread
          (lineThrough configuration.second configuration.first
            configuration.firstSecondDistinct.symm)
          secondSide reversedFirstSideNonNull
          configuration.secondThirdNonNull / d at law
    rw [apexCanonical] at law
    exact law
  have secondSpreadLaw : apex / d = baseThird / r := by
    have law := spreadLaws.2
    change
      spread
          (lineThrough configuration.second configuration.first
            configuration.firstSecondDistinct.symm)
          secondSide reversedFirstSideNonNull
          configuration.secondThirdNonNull / d =
        spread
          (lineThrough configuration.third configuration.first
            configuration.firstThirdDistinct.symm)
          (lineThrough configuration.third configuration.second
            configuration.secondThirdDistinct.symm)
          reversedDiagonalNonNull reversedSecondSideNonNull / r at law
    rw [apexCanonical, baseThirdCanonical] at law
    exact law
  have baseSpreadsEqual : baseFirst = baseThird := by
    calc
      baseFirst = (baseFirst / r) * r :=
        (RFAP.ExplicitField.div_mul_cancel baseFirst rNonzero).symm
      _ = (baseThird / r) * r := by rw [firstSpreadLaw, secondSpreadLaw]
      _ = baseThird := RFAP.ExplicitField.div_mul_cancel baseThird rNonzero
  have equalSpreadAlternatives :
      apex = 0 ∨ apex = 4 * baseFirst * (1 - baseFirst) := by
    have alternatives := equal_spreads firstSide diagonal secondSide
      configuration.firstSecondNonNull configuration.firstThirdNonNull
      configuration.secondThirdNonNull baseSpreadsEqual
    exact alternatives
  have scalarConclusion := polygon_triangle_scalars q r d value baseFirst apex
    baseThird qNonzero rNonzero dNonzero valueNonzero baseFirstNonzero
    apexNonzero twoNonzero firstSideValue diagonalValue firstSpreadLaw
    secondSpreadLaw equalSpreadAlternatives
  rcases scalarConclusion with
    ⟨sideFormula, diagonalFormula, firstSpreadValue,
      thirdSpreadValue, apexSpreadValue⟩
  exact ⟨sideFormula, secondSideValue, diagonalFormula,
    firstSpreadValue, thirdSpreadValue, apexSpreadValue⟩

/-- Exercise 14.2: at any requested finite index `k`, reflecting `A₀` in the
star line `lₖ` gives the polygon vertex `A₂ₖ`, whose quadrance from `A₀` is
`4 Sₖ(s) Q`.  The caller supplies the already-computed finite spread value of
`l₀,lₖ`; no infinite point or line sequence is formed. -/
theorem exercise_14_2 [DecidableEq K]
    (index : Nat) (value : K) (center initialPoint : Point K)
    (centerInitialDistinct : center ≠ initialPoint)
    (initialRadialNonNull :
      ¬ (lineThrough center initialPoint centerInitialDistinct).IsNull)
    (mirror : Line K) (mirrorNonNull : ¬ mirror.IsNull)
    (centerOnMirror : mirror.Contains center)
    (indexedSpread :
      spread (lineThrough center initialPoint centerInitialDistinct) mirror
          initialRadialNonNull mirrorNonNull =
        spreadPolynomial index value) :
    quadrance initialPoint (reflectPoint mirror mirrorNonNull initialPoint) =
      4 * spreadPolynomial index value * quadrance center initialPoint := by
  calc
    quadrance initialPoint (reflectPoint mirror mirrorNonNull initialPoint) =
        4 * spread (lineThrough center initialPoint centerInitialDistinct)
          mirror initialRadialNonNull mirrorNonNull *
            quadrance center initialPoint :=
      reflectPoint_chord_quadrance_eq_spread center initialPoint
        centerInitialDistinct initialRadialNonNull mirror mirrorNonNull
        centerOnMirror
    _ = 4 * spreadPolynomial index value * quadrance center initialPoint := by
      rw [indexedSpread]

end DivineProportions
