import DivineProportions.Curves.Taylor
import DivineProportions.Trigonometry.Spread

/-!
# Divine Proportions, §19.4: the folium of Descartes

The folium, its rational parametrization, first- and second-order tangent
formulae, and the reciprocal-parameter spread symmetry are all finite
polynomial constructions.  Denominators and the characteristic-three
exception are exposed as explicit hypotheses.
-/

namespace DivineProportions

namespace Folium

variable {K : Type*} [RFAP.ExplicitField K]

/-- The folium of Descartes `x³+y³+3xy=0`. -/
def curve [Nontrivial K] : CubicCurve K where
  g := 1
  h := 0
  i := 0
  j := 1
  d := 0
  e := 3
  f := 0
  a := 0
  b := 0
  c := 0
  cubic_nonzero := Or.inl one_ne_zero

/-- The denominator `1+t³` in equation (19.3). -/
def parameterDenominator (parameter : K) : K :=
  1 + parameter ^ 3

/-- Equation (19.3), as an executable point whenever its displayed
denominator is nonzero. -/
def parameterPoint (parameter : K) : Point K :=
  ⟨(-3 * parameter) / parameterDenominator parameter,
    (-3 * parameter ^ 2) / parameterDenominator parameter⟩

private theorem inverse_as_denominator_times_inverse_square
    {denominator : K} (denominatorNonzero : denominator ≠ 0) :
    denominator⁻¹ = denominator * denominator⁻¹ ^ 2 := by
  have cancel : denominator * denominator⁻¹ = (1 : K) :=
    RFAP.ExplicitField.mul_inv_cancel denominator denominatorNonzero
  calc
    denominator⁻¹ = 1 * denominator⁻¹ := by ring1
    _ = (denominator * denominator⁻¹) * denominator⁻¹ := by
      rw [cancel]
    _ = denominator * denominator⁻¹ ^ 2 := by ring1

private theorem one_as_denominator_square_times_inverse_square
    {denominator : K} (denominatorNonzero : denominator ≠ 0) :
    (1 : K) = denominator ^ 2 * denominator⁻¹ ^ 2 := by
  have cancel : denominator * denominator⁻¹ = (1 : K) :=
    RFAP.ExplicitField.mul_inv_cancel denominator denominatorNonzero
  calc
    (1 : K) = (denominator * denominator⁻¹) ^ 2 := by
      rw [cancel]
      ring1
    _ = denominator ^ 2 * denominator⁻¹ ^ 2 := by ring1

private theorem clear_quadratic_denominator
    {denominator quadratic linear constant : K}
    (denominatorNonzero : denominator ≠ 0) :
    quadratic * denominator⁻¹ ^ 2 + linear * denominator⁻¹ + constant =
      (quadratic + linear * denominator + constant * denominator ^ 2) *
        denominator⁻¹ ^ 2 := by
  have cancel : denominator * denominator⁻¹ = (1 : K) :=
    RFAP.ExplicitField.mul_inv_cancel denominator denominatorNonzero
  calc
    quadratic * denominator⁻¹ ^ 2 + linear * denominator⁻¹ + constant =
        (quadratic + linear * denominator + constant * denominator ^ 2) *
            denominator⁻¹ ^ 2 +
          linear * denominator⁻¹ *
            (1 - denominator * denominator⁻¹) +
          constant * (1 - (denominator * denominator⁻¹) ^ 2) := by
      ring1
    _ = (quadratic + linear * denominator + constant * denominator ^ 2) *
        denominator⁻¹ ^ 2 := by rw [cancel]; ring1

/-- The displayed cubic equation is recovered exactly. -/
theorem evaluate_curve [Nontrivial K] (point : Point K) :
    (curve (K := K)).evaluate point =
      point.x ^ 3 + point.y ^ 3 + 3 * point.x * point.y := by
  unfold curve CubicCurve.evaluate
  ring1

/-- Converse half of equation (19.3): every allowed parameter produces a
point of the folium. -/
theorem parameterPoint_contains [Nontrivial K]
    (parameter : K)
    (denominatorNonzero : parameterDenominator parameter ≠ 0) :
    (curve (K := K)).Contains (parameterPoint parameter) := by
  let denominator := parameterDenominator parameter
  have cancel : denominator * denominator⁻¹ = (1 : K) :=
    RFAP.ExplicitField.mul_inv_cancel denominator denominatorNonzero
  unfold CubicCurve.Contains parameterPoint
  rw [evaluate_curve]
  simp only [RFAP.ExplicitField.div_eq_mul_inv]
  change
    ((-3 * parameter) * denominator⁻¹) ^ 3 +
        ((-3 * parameter ^ 2) * denominator⁻¹) ^ 3 +
        3 * ((-3 * parameter) * denominator⁻¹) *
          ((-3 * parameter ^ 2) * denominator⁻¹) = 0
  calc
    ((-3 * parameter) * denominator⁻¹) ^ 3 +
          ((-3 * parameter ^ 2) * denominator⁻¹) ^ 3 +
          3 * ((-3 * parameter) * denominator⁻¹) *
            ((-3 * parameter ^ 2) * denominator⁻¹) =
        27 * parameter ^ 3 * denominator⁻¹ ^ 2 *
          (1 - denominator * denominator⁻¹) := by
      unfold denominator parameterDenominator
      ring1
    _ = 0 := by rw [cancel]; ring1

private theorem tangentDirection_nonzero [Nontrivial K] [DecidableEq K]
    (parameter : K) (threeNonzero : (3 : K) ≠ 0) :
    parameter * (2 - parameter ^ 3) ≠ 0 ∨
      2 * parameter ^ 3 - 1 ≠ 0 := by
  by_cases firstZero : parameter * (2 - parameter ^ 3) = 0
  · right
    intro secondZero
    have parameterNonzero : parameter ≠ 0 := by
      intro parameterZero
      have oneZero : (1 : K) = 0 := by
        calc
          (1 : K) = -(2 * parameter ^ 3 - 1) := by rw [parameterZero]; ring1
          _ = 0 := by rw [secondZero]; ring1
      exact one_ne_zero oneZero
    have threeTimesParameterZero : (3 : K) * parameter = 0 := by
      calc
        (3 : K) * parameter =
            2 * (parameter * (2 - parameter ^ 3)) +
              parameter * (2 * parameter ^ 3 - 1) := by ring1
        _ = 0 := by rw [firstZero, secondZero]; ring1
    exact
      (RFAP.ExplicitField.mul_ne_zero threeNonzero parameterNonzero)
        threeTimesParameterZero
  · exact Or.inl firstZero

/-- Equation (19.5), retaining the representative printed by the source. -/
def tangentLine [Nontrivial K] [DecidableEq K]
    (parameter : K) (threeNonzero : (3 : K) ≠ 0) : Line K where
  a := parameter * (2 - parameter ^ 3)
  b := 2 * parameter ^ 3 - 1
  c := 3 * parameter ^ 2
  direction_nonzero := tangentDirection_nonzero parameter threeNonzero

/-- The printed tangent representative passes through its parameter point,
including at `t=0` where the cubic itself is singular. -/
theorem tangentLine_contains [Nontrivial K] [DecidableEq K]
    (parameter : K) (threeNonzero : (3 : K) ≠ 0)
    (denominatorNonzero : parameterDenominator parameter ≠ 0) :
    (tangentLine parameter threeNonzero).Contains (parameterPoint parameter) := by
  let denominator := parameterDenominator parameter
  have cancel : denominator * denominator⁻¹ = (1 : K) :=
    RFAP.ExplicitField.mul_inv_cancel denominator denominatorNonzero
  unfold tangentLine Line.Contains parameterPoint
  simp only [RFAP.ExplicitField.div_eq_mul_inv]
  change
    parameter * (2 - parameter ^ 3) *
          ((-3 * parameter) * denominator⁻¹) +
        (2 * parameter ^ 3 - 1) *
          ((-3 * parameter ^ 2) * denominator⁻¹) +
        3 * parameter ^ 2 = 0
  calc
    parameter * (2 - parameter ^ 3) *
          ((-3 * parameter) * denominator⁻¹) +
        (2 * parameter ^ 3 - 1) *
          ((-3 * parameter ^ 2) * denominator⁻¹) +
        3 * parameter ^ 2 =
      3 * parameter ^ 2 * (1 - denominator * denominator⁻¹) := by
        unfold denominator parameterDenominator
        ring1
    _ = 0 := by rw [cancel]; ring1

/-- The nonzero scale relating the Taylor gradient to equation (19.5). -/
def tangentScale (parameter : K) : K :=
  9 * parameter * (parameterDenominator parameter)⁻¹ ^ 2

private theorem tangentScale_nonzero [Nontrivial K]
    (parameter : K) (threeNonzero : (3 : K) ≠ 0)
    (parameterNonzero : parameter ≠ 0)
    (denominatorNonzero : parameterDenominator parameter ≠ 0) :
    tangentScale parameter ≠ 0 := by
  have nineNonzero : (9 : K) ≠ 0 := by
    have threeSquaredNonzero : (3 : K) * 3 ≠ 0 :=
      RFAP.ExplicitField.mul_ne_zero threeNonzero threeNonzero
    intro nineZero
    apply threeSquaredNonzero
    calc
      (3 : K) * 3 = 9 := by ring1
      _ = 0 := nineZero
  have inverseNonzero :
      (parameterDenominator parameter)⁻¹ ≠ 0 :=
    RFAP.ExplicitField.inv_ne_zero denominatorNonzero
  have inverseSquareNonzero :
      (parameterDenominator parameter)⁻¹ ^ 2 ≠ 0 := by
    simpa only [pow_two] using
      RFAP.ExplicitField.mul_ne_zero inverseNonzero inverseNonzero
  exact RFAP.ExplicitField.mul_ne_zero
    (RFAP.ExplicitField.mul_ne_zero nineNonzero parameterNonzero)
    inverseSquareNonzero

/-- The first Taylor coefficient at (19.3) is the first coefficient of
(19.5), multiplied by the explicit common scale. -/
theorem taylorA_parameterPoint [Nontrivial K]
    (parameter : K)
    (denominatorNonzero : parameterDenominator parameter ≠ 0) :
    CubicCurve.taylorA (curve (K := K)) (parameterPoint parameter) =
      tangentScale parameter * (parameter * (2 - parameter ^ 3)) := by
  let denominator := parameterDenominator parameter
  rw [show CubicCurve.taylorA (curve (K := K)) (parameterPoint parameter) =
      3 * (parameterPoint parameter).x ^ 2 +
        3 * (parameterPoint parameter).y by
    unfold CubicCurve.taylorA curve
    ring1]
  unfold parameterPoint tangentScale
  simp only [RFAP.ExplicitField.div_eq_mul_inv]
  calc
    3 * ((-3 * parameter) * denominator⁻¹) ^ 2 +
          3 * ((-3 * parameter ^ 2) * denominator⁻¹) =
        27 * parameter ^ 2 * denominator⁻¹ ^ 2 -
          9 * parameter ^ 2 * denominator⁻¹ := by
      ring1
    _ =
        (27 * parameter ^ 2 - 9 * parameter ^ 2 * denominator) *
          denominator⁻¹ ^ 2 := by
      calc
        27 * parameter ^ 2 * denominator⁻¹ ^ 2 -
            9 * parameter ^ 2 * denominator⁻¹ =
          27 * parameter ^ 2 * denominator⁻¹ ^ 2 +
            (-9 * parameter ^ 2) * denominator⁻¹ + 0 := by ring1
        _ = (27 * parameter ^ 2 +
              (-9 * parameter ^ 2) * denominator + 0 * denominator ^ 2) *
            denominator⁻¹ ^ 2 :=
          clear_quadratic_denominator denominatorNonzero
        _ = (27 * parameter ^ 2 - 9 * parameter ^ 2 * denominator) *
            denominator⁻¹ ^ 2 := by ring1
    _ = 9 * parameter * denominator⁻¹ ^ 2 *
        (parameter * (2 - parameter ^ 3)) := by
      unfold denominator parameterDenominator
      ring1

/-- The second Taylor coefficient at (19.3) is the second coefficient of
(19.5), multiplied by the same explicit scale. -/
theorem taylorB_parameterPoint [Nontrivial K]
    (parameter : K)
    (denominatorNonzero : parameterDenominator parameter ≠ 0) :
    CubicCurve.taylorB (curve (K := K)) (parameterPoint parameter) =
      tangentScale parameter * (2 * parameter ^ 3 - 1) := by
  let denominator := parameterDenominator parameter
  rw [show CubicCurve.taylorB (curve (K := K)) (parameterPoint parameter) =
      3 * (parameterPoint parameter).x +
        3 * (parameterPoint parameter).y ^ 2 by
    unfold CubicCurve.taylorB curve
    ring1]
  unfold parameterPoint tangentScale
  simp only [RFAP.ExplicitField.div_eq_mul_inv]
  calc
    3 * ((-3 * parameter) * denominator⁻¹) +
          3 * ((-3 * parameter ^ 2) * denominator⁻¹) ^ 2 =
        27 * parameter ^ 4 * denominator⁻¹ ^ 2 -
          9 * parameter * denominator⁻¹ := by
      ring1
    _ =
        (27 * parameter ^ 4 - 9 * parameter * denominator) *
          denominator⁻¹ ^ 2 := by
      calc
        27 * parameter ^ 4 * denominator⁻¹ ^ 2 -
            9 * parameter * denominator⁻¹ =
          27 * parameter ^ 4 * denominator⁻¹ ^ 2 +
            (-9 * parameter) * denominator⁻¹ + 0 := by ring1
        _ = (27 * parameter ^ 4 +
              (-9 * parameter) * denominator + 0 * denominator ^ 2) *
            denominator⁻¹ ^ 2 :=
          clear_quadratic_denominator denominatorNonzero
        _ = (27 * parameter ^ 4 - 9 * parameter * denominator) *
            denominator⁻¹ ^ 2 := by ring1
    _ = 9 * parameter * denominator⁻¹ ^ 2 *
        (2 * parameter ^ 3 - 1) := by
      unfold denominator parameterDenominator
      ring1

/-- Every allowed nonzero folium parameter is first-order nonsingular. -/
theorem firstOrderNonSingular_parameterPoint
    [Nontrivial K] [DecidableEq K]
    (parameter : K) (threeNonzero : (3 : K) ≠ 0)
    (parameterNonzero : parameter ≠ 0)
    (denominatorNonzero : parameterDenominator parameter ≠ 0) :
    (curve (K := K)).IsFirstOrderNonSingularAt
      (parameterPoint parameter) := by
  have scaleNonzero := tangentScale_nonzero parameter threeNonzero
    parameterNonzero denominatorNonzero
  rcases (tangentLine parameter threeNonzero).direction_nonzero with
    firstNonzero | secondNonzero
  · left
    rw [taylorA_parameterPoint parameter denominatorNonzero]
    exact RFAP.ExplicitField.mul_ne_zero scaleNonzero firstNonzero
  · right
    rw [taylorB_parameterPoint parameter denominatorNonzero]
    exact RFAP.ExplicitField.mul_ne_zero scaleNonzero secondNonzero

/-- Equation (19.5) is exactly the first-order tangent produced by the
general cubic Taylor construction, up to its displayed common scale. -/
theorem tangentLine_formula [Nontrivial K] [DecidableEq K]
    (parameter : K) (threeNonzero : (3 : K) ≠ 0)
    (parameterNonzero : parameter ≠ 0)
    (denominatorNonzero : parameterDenominator parameter ≠ 0) :
    let nonSingular := firstOrderNonSingular_parameterPoint parameter
      threeNonzero parameterNonzero denominatorNonzero
    (CubicCurve.tangentLine (curve (K := K)) (parameterPoint parameter)
        nonSingular).Equivalent
      (tangentLine parameter threeNonzero) := by
  dsimp only
  let nonSingular := firstOrderNonSingular_parameterPoint parameter
    threeNonzero parameterNonzero denominatorNonzero
  let taylorLine := CubicCurve.tangentLine (curve (K := K))
    (parameterPoint parameter) nonSingular
  let printedLine := tangentLine parameter threeNonzero
  have firstCoefficient :
      taylorLine.a = tangentScale parameter * printedLine.a := by
    unfold taylorLine printedLine CubicCurve.tangentLine tangentLine
    exact taylorA_parameterPoint parameter denominatorNonzero
  have secondCoefficient :
      taylorLine.b = tangentScale parameter * printedLine.b := by
    unfold taylorLine printedLine CubicCurve.tangentLine tangentLine
    exact taylorB_parameterPoint parameter denominatorNonzero
  have printedContains : printedLine.Contains (parameterPoint parameter) := by
    exact tangentLine_contains parameter threeNonzero denominatorNonzero
  have constantCoefficient :
      taylorLine.c = tangentScale parameter * printedLine.c := by
    have constantDefinition :
        taylorLine.c =
          -taylorLine.a * (parameterPoint parameter).x -
            taylorLine.b * (parameterPoint parameter).y := by
      rfl
    rw [constantDefinition, firstCoefficient, secondCoefficient]
    unfold Line.Contains at printedContains
    calc
      -(tangentScale parameter * printedLine.a) *
            (parameterPoint parameter).x -
          tangentScale parameter * printedLine.b *
            (parameterPoint parameter).y =
        tangentScale parameter * printedLine.c -
          tangentScale parameter *
            (printedLine.a * (parameterPoint parameter).x +
              printedLine.b * (parameterPoint parameter).y + printedLine.c) := by
        ring1
      _ = tangentScale parameter * printedLine.c := by
        rw [printedContains]
        ring1
  unfold Line.Equivalent
  rw [firstCoefficient, secondCoefficient, constantCoefficient]
  exact ⟨by ring1, by ring1, by ring1⟩

private theorem negative_square_nonzero
    {value : K} (valueNonzero : value ≠ 0) : -(value ^ 2) ≠ 0 := by
  have squareNonzero : value * value ≠ 0 :=
    RFAP.ExplicitField.mul_ne_zero valueNonzero valueNonzero
  intro negativeSquareZero
  apply squareNonzero
  calc
    value * value = value ^ 2 := by ring1
    _ = -(-(value ^ 2)) := by ring1
    _ = 0 := by rw [negativeSquareZero]; ring1

/-- Equation (19.6), the second-order tangent conic in the source's cleared
coefficient representative. -/
def tangentConic [Nontrivial K]
    (parameter : K)
    (denominatorNonzero : parameterDenominator parameter ≠ 0) : Conic K where
  d := 3 * parameter * parameterDenominator parameter
  e := -(parameterDenominator parameter ^ 2)
  f := 3 * parameter ^ 2 * parameterDenominator parameter
  a := 9 * parameter ^ 2
  b := 9 * parameter ^ 4
  c := 9 * parameter ^ 3
  quadratic_nonzero :=
    Or.inr (Or.inl (negative_square_nonzero denominatorNonzero))

/-- The conic (19.6) contains the point at which it is tangent. -/
theorem tangentConic_contains [Nontrivial K]
    (parameter : K)
    (denominatorNonzero : parameterDenominator parameter ≠ 0) :
    (tangentConic parameter denominatorNonzero).Contains
      (parameterPoint parameter) := by
  let denominator := parameterDenominator parameter
  unfold tangentConic Conic.Contains Conic.evaluate parameterPoint
  simp only [RFAP.ExplicitField.div_eq_mul_inv]
  change
    (3 * parameter * denominator) *
          (((-3 * parameter) * denominator⁻¹) ^ 2) +
        (-(denominator ^ 2)) *
          ((-3 * parameter) * denominator⁻¹) *
          ((-3 * parameter ^ 2) * denominator⁻¹) +
        (3 * parameter ^ 2 * denominator) *
          (((-3 * parameter ^ 2) * denominator⁻¹) ^ 2) +
        9 * parameter ^ 2 *
          ((-3 * parameter) * denominator⁻¹) +
        9 * parameter ^ 4 *
          ((-3 * parameter ^ 2) * denominator⁻¹) +
        9 * parameter ^ 3 = 0
  let quadratic :=
    27 * parameter ^ 3 * denominator -
      9 * denominator ^ 2 * parameter ^ 3 +
      27 * parameter ^ 6 * denominator
  let linear := -27 * parameter ^ 3 - 27 * parameter ^ 6
  let constant := 9 * parameter ^ 3
  calc
    (3 * parameter * denominator) *
            (((-3 * parameter) * denominator⁻¹) ^ 2) +
          (-(denominator ^ 2)) *
            ((-3 * parameter) * denominator⁻¹) *
            ((-3 * parameter ^ 2) * denominator⁻¹) +
          (3 * parameter ^ 2 * denominator) *
            (((-3 * parameter ^ 2) * denominator⁻¹) ^ 2) +
          9 * parameter ^ 2 *
            ((-3 * parameter) * denominator⁻¹) +
          9 * parameter ^ 4 *
            ((-3 * parameter ^ 2) * denominator⁻¹) +
          9 * parameter ^ 3 =
        quadratic * denominator⁻¹ ^ 2 +
          linear * denominator⁻¹ + constant := by
      unfold quadratic linear constant
      ring1
    _ = (quadratic + linear * denominator + constant * denominator ^ 2) *
        denominator⁻¹ ^ 2 :=
      clear_quadratic_denominator denominatorNonzero
    _ = 0 := by
      have cleared :
          quadratic + linear * denominator + constant * denominator ^ 2 = 0 := by
        unfold quadratic linear constant denominator parameterDenominator
        ring1
      rw [cleared]
      ring1

/-- The mixed quadratic Taylor coefficient is constantly `3`, so every
parameter point is second-order nonsingular when the characteristic is not
three. -/
theorem secondOrderNonSingular_parameterPoint [Nontrivial K]
    (parameter : K) (threeNonzero : (3 : K) ≠ 0) :
    (curve (K := K)).IsSecondOrderNonSingularAt
      (parameterPoint parameter) := by
  right
  left
  unfold CubicCurve.taylorE curve parameterPoint
  simpa only [zero_mul, add_zero, mul_zero] using threeNonzero

/-- Equation (19.6) is the general second-order Taylor conic.  The equality
is recorded coefficientwise after clearing the common nonzero scale:
`3·(printed coefficient) = -(1+t³)²·(Taylor coefficient)`. -/
theorem tangentConic_formula_cleared [Nontrivial K]
    (parameter : K) (threeNonzero : (3 : K) ≠ 0)
    (denominatorNonzero : parameterDenominator parameter ≠ 0) :
    let secondOrder :=
      secondOrderNonSingular_parameterPoint (K := K) parameter threeNonzero
    let taylor := CubicCurve.tangentConic (curve (K := K))
      (parameterPoint parameter) secondOrder
    let printed := tangentConic parameter denominatorNonzero
    3 * printed.d = -(parameterDenominator parameter ^ 2) * taylor.d ∧
      3 * printed.e = -(parameterDenominator parameter ^ 2) * taylor.e ∧
      3 * printed.f = -(parameterDenominator parameter ^ 2) * taylor.f ∧
      3 * printed.a = -(parameterDenominator parameter ^ 2) * taylor.a ∧
      3 * printed.b = -(parameterDenominator parameter ^ 2) * taylor.b ∧
      3 * printed.c = -(parameterDenominator parameter ^ 2) * taylor.c := by
  dsimp only
  let denominator := parameterDenominator parameter
  let secondOrder :=
    secondOrderNonSingular_parameterPoint (K := K) parameter threeNonzero
  let taylor := CubicCurve.tangentConic (curve (K := K))
    (parameterPoint parameter) secondOrder
  let printed := tangentConic parameter denominatorNonzero
  have cancel : denominator * denominator⁻¹ = (1 : K) :=
    RFAP.ExplicitField.mul_inv_cancel denominator denominatorNonzero
  have denominatorSquareInverse :
      denominator ^ 2 * denominator⁻¹ = denominator := by
    calc
      denominator ^ 2 * denominator⁻¹ =
          denominator * (denominator * denominator⁻¹) := by ring1
      _ = denominator := by rw [cancel]; ring1
  have denominatorSquareInverseSquare :
      denominator ^ 2 * denominator⁻¹ ^ 2 = (1 : K) := by
    calc
      denominator ^ 2 * denominator⁻¹ ^ 2 =
          (denominator * denominator⁻¹) ^ 2 := by ring1
      _ = 1 := by rw [cancel]; ring1
  have taylorD : taylor.d = -9 * parameter * denominator⁻¹ := by
    unfold taylor CubicCurve.tangentConic Conic.translateConic
      CubicCurve.standardTangentConic CubicCurve.taylorD curve parameterPoint
    simp only [RFAP.ExplicitField.div_eq_mul_inv]
    ring1
  have taylorE : taylor.e = 3 := by
    unfold taylor CubicCurve.tangentConic Conic.translateConic
      CubicCurve.standardTangentConic CubicCurve.taylorE curve
    ring1
  have taylorF : taylor.f = -9 * parameter ^ 2 * denominator⁻¹ := by
    unfold taylor CubicCurve.tangentConic Conic.translateConic
      CubicCurve.standardTangentConic CubicCurve.taylorF curve parameterPoint
    simp only [RFAP.ExplicitField.div_eq_mul_inv]
    ring1
  have taylorA : taylor.a = -27 * parameter ^ 2 * denominator⁻¹ ^ 2 := by
    unfold taylor CubicCurve.tangentConic Conic.translateConic
      CubicCurve.standardTangentConic CubicCurve.taylorD CubicCurve.taylorE
      CubicCurve.taylorA curve parameterPoint
    simp only [RFAP.ExplicitField.div_eq_mul_inv]
    ring1
  have taylorB : taylor.b = -27 * parameter ^ 4 * denominator⁻¹ ^ 2 := by
    unfold taylor CubicCurve.tangentConic Conic.translateConic
      CubicCurve.standardTangentConic CubicCurve.taylorE CubicCurve.taylorF
      CubicCurve.taylorB curve parameterPoint
    simp only [RFAP.ExplicitField.div_eq_mul_inv]
    ring1
  have taylorC : taylor.c = -27 * parameter ^ 3 * denominator⁻¹ ^ 2 := by
    unfold taylor CubicCurve.tangentConic Conic.translateConic
      CubicCurve.standardTangentConic CubicCurve.taylorD CubicCurve.taylorE
      CubicCurve.taylorF CubicCurve.taylorA CubicCurve.taylorB curve
      parameterPoint
    simp only [RFAP.ExplicitField.div_eq_mul_inv]
    ring1
  dsimp only [tangentConic]
  change
    3 * (3 * parameter * denominator) = -(denominator ^ 2) * taylor.d ∧
      3 * (-(denominator ^ 2)) = -(denominator ^ 2) * taylor.e ∧
      3 * (3 * parameter ^ 2 * denominator) =
        -(denominator ^ 2) * taylor.f ∧
      3 * (9 * parameter ^ 2) = -(denominator ^ 2) * taylor.a ∧
      3 * (9 * parameter ^ 4) = -(denominator ^ 2) * taylor.b ∧
      3 * (9 * parameter ^ 3) = -(denominator ^ 2) * taylor.c
  rw [taylorD, taylorE, taylorF, taylorA, taylorB, taylorC]
  constructor
  · calc
      3 * (3 * parameter * denominator) =
          9 * parameter * denominator := by ring1
      _ = 9 * parameter * (denominator ^ 2 * denominator⁻¹) := by
        rw [denominatorSquareInverse]
      _ = -(denominator ^ 2) * (-9 * parameter * denominator⁻¹) := by
        ring1
  · constructor
    · ring1
    · constructor
      · calc
          3 * (3 * parameter ^ 2 * denominator) =
              9 * parameter ^ 2 * denominator := by ring1
          _ = 9 * parameter ^ 2 *
              (denominator ^ 2 * denominator⁻¹) := by
            rw [denominatorSquareInverse]
          _ = -(denominator ^ 2) *
              (-9 * parameter ^ 2 * denominator⁻¹) := by ring1
      · constructor
        · calc
            3 * (9 * parameter ^ 2) = 27 * parameter ^ 2 := by ring1
            _ = 27 * parameter ^ 2 *
                (denominator ^ 2 * denominator⁻¹ ^ 2) := by
              rw [denominatorSquareInverseSquare]
              ring1
            _ = -(denominator ^ 2) *
                (-27 * parameter ^ 2 * denominator⁻¹ ^ 2) := by ring1
        · constructor
          · calc
              3 * (9 * parameter ^ 4) = 27 * parameter ^ 4 := by ring1
              _ = 27 * parameter ^ 4 *
                  (denominator ^ 2 * denominator⁻¹ ^ 2) := by
                rw [denominatorSquareInverseSquare]
                ring1
              _ = -(denominator ^ 2) *
                  (-27 * parameter ^ 4 * denominator⁻¹ ^ 2) := by ring1
          · calc
              3 * (9 * parameter ^ 3) = 27 * parameter ^ 3 := by ring1
              _ = 27 * parameter ^ 3 *
                  (denominator ^ 2 * denominator⁻¹ ^ 2) := by
                rw [denominatorSquareInverseSquare]
                ring1
              _ = -(denominator ^ 2) *
                  (-27 * parameter ^ 3 * denominator⁻¹ ^ 2) := by ring1

/-- At the singular parameter `t=0`, equation (19.6) is the pair of lines
`xy=0`, up to the harmless nonzero coefficient `-1`. -/
theorem tangentConic_at_zero [Nontrivial K]
    (oneNonzero : parameterDenominator (0 : K) ≠ 0) :
    let conic := tangentConic (0 : K) oneNonzero
    conic.d = 0 ∧ conic.e = -1 ∧ conic.f = 0 ∧
      conic.a = 0 ∧ conic.b = 0 ∧ conic.c = 0 ∧
      ∀ point : Point K, conic.evaluate point = -(point.x * point.y) := by
  dsimp only [tangentConic, parameterDenominator]
  refine ⟨by ring1, by ring1, by ring1, by ring1, by ring1, by ring1, ?_⟩
  intro point
  unfold Conic.evaluate
  ring1

/-- The polynomial controlling the determinant in Example 19.8. -/
def determinantPolynomial (parameter : K) : K :=
  parameter ^ 6 - 34 * parameter ^ 3 + 1

/-- Example 19.8's matrix determinant, with the factor `1/4` cleared:
`4 det M = -(t⁶-34t³+1)`. -/
theorem four_mul_associatedMatrixDeterminant (parameter : K) :
    4 * (3 * parameter * (3 * parameter ^ 2)) -
        (-(parameterDenominator parameter)) ^ 2 =
      -(determinantPolynomial parameter) := by
  unfold parameterDenominator determinantPolynomial
  ring1

/-- The two displayed quadratic roots in Example 19.8 are roots whenever an
explicit square root of `2` is supplied. -/
theorem determinant_quadratic_roots
    (rootTwo : K) (rootTwoSquared : rootTwo ^ 2 = 2) :
    let lower := 17 - 12 * rootTwo
    let upper := 17 + 12 * rootTwo
    lower ^ 2 - 34 * lower + 1 = 0 ∧
      upper ^ 2 - 34 * upper + 1 = 0 ∧ lower * upper = 1 := by
  dsimp only
  constructor
  · rw [show (17 - 12 * rootTwo) ^ 2 - 34 * (17 - 12 * rootTwo) + 1 =
        144 * (rootTwo ^ 2 - 2) by ring1,
      rootTwoSquared]
    ring1
  · constructor
    · rw [show (17 + 12 * rootTwo) ^ 2 - 34 * (17 + 12 * rootTwo) + 1 =
          144 * (rootTwo ^ 2 - 2) by ring1,
        rootTwoSquared]
      ring1
    · rw [show (17 - 12 * rootTwo) * (17 + 12 * rootTwo) =
          289 - 144 * rootTwo ^ 2 by ring1,
        rootTwoSquared]
      ring1

/-- A cube root of either displayed quadratic root makes the determinant
polynomial vanish.  No completed real-number or order structure is used. -/
theorem determinantPolynomial_eq_zero_of_cube_root
    (parameter root : K)
    (rootEquation : root ^ 2 - 34 * root + 1 = 0)
    (cubeRoot : parameter ^ 3 = root) :
    determinantPolynomial parameter = 0 := by
  unfold determinantPolynomial
  rw [show parameter ^ 6 = (parameter ^ 3) ^ 2 by ring1, cubeRoot]
  exact rootEquation

/-- Exercise 19.4, first assertion: the tangent conic at parameter `t`
passes through the point at parameter `u` whenever `(tu)³=1`. -/
theorem tangentConic_contains_of_parameter_product_cube [Nontrivial K]
    (parameter reciprocalParameter : K)
    (parameterDenominatorNonzero : parameterDenominator parameter ≠ 0)
    (reciprocalDenominatorNonzero :
      parameterDenominator reciprocalParameter ≠ 0)
    (productCube : (parameter * reciprocalParameter) ^ 3 = 1) :
    (tangentConic parameter parameterDenominatorNonzero).Contains
      (parameterPoint reciprocalParameter) := by
  let denominator := parameterDenominator reciprocalParameter
  let quadratic :=
    27 * parameter * parameterDenominator parameter *
        reciprocalParameter ^ 2 -
      9 * parameterDenominator parameter ^ 2 *
        reciprocalParameter ^ 3 +
      27 * parameter ^ 2 * parameterDenominator parameter *
        reciprocalParameter ^ 4
  let linear :=
    -27 * parameter ^ 2 * reciprocalParameter -
      27 * parameter ^ 4 * reciprocalParameter ^ 2
  let constant := 9 * parameter ^ 3
  unfold Conic.Contains tangentConic Conic.evaluate parameterPoint
  simp only [RFAP.ExplicitField.div_eq_mul_inv]
  calc
    3 * parameter * parameterDenominator parameter *
              (-3 * reciprocalParameter *
                (parameterDenominator reciprocalParameter)⁻¹) ^ 2 +
            -parameterDenominator parameter ^ 2 *
                (-3 * reciprocalParameter *
                  (parameterDenominator reciprocalParameter)⁻¹) *
              (-3 * reciprocalParameter ^ 2 *
                (parameterDenominator reciprocalParameter)⁻¹) +
          3 * parameter ^ 2 * parameterDenominator parameter *
            (-3 * reciprocalParameter ^ 2 *
              (parameterDenominator reciprocalParameter)⁻¹) ^ 2 +
        9 * parameter ^ 2 *
          (-3 * reciprocalParameter *
            (parameterDenominator reciprocalParameter)⁻¹) +
      9 * parameter ^ 4 *
          (-3 * reciprocalParameter ^ 2 *
            (parameterDenominator reciprocalParameter)⁻¹) +
        9 * parameter ^ 3 =
      quadratic * denominator⁻¹ ^ 2 +
        linear * denominator⁻¹ + constant := by
      unfold quadratic linear constant denominator
      ring1
    _ = (quadratic + linear * denominator + constant * denominator ^ 2) *
        denominator⁻¹ ^ 2 :=
      clear_quadratic_denominator reciprocalDenominatorNonzero
    _ = 0 := by
      have clearedZero :
          quadratic + linear * denominator + constant * denominator ^ 2 = 0 := by
        calc
          quadratic + linear * denominator + constant * denominator ^ 2 =
              9 * (1 - (parameter * reciprocalParameter) ^ 3) *
                (3 * parameter * reciprocalParameter ^ 2 -
                  reciprocalParameter ^ 3 + parameter ^ 3 -
                  3 * parameter ^ 2 * reciprocalParameter) := by
            unfold quadratic linear constant denominator parameterDenominator
            ring1
          _ = 0 := by rw [productCube]; ring1
      rw [clearedZero]
      ring1

/-- First denominator-cleared direction coefficient of the tangent to the
tangent conic at `t`, evaluated at the point with parameter `u`. -/
def crossTangentA (parameter otherParameter : K) : K :=
  9 * parameter ^ 2 * parameterDenominator otherParameter -
    18 * parameter * parameterDenominator parameter * otherParameter +
    3 * parameterDenominator parameter ^ 2 * otherParameter ^ 2

/-- Second denominator-cleared direction coefficient of the same tangent. -/
def crossTangentB (parameter otherParameter : K) : K :=
  9 * parameter ^ 4 * parameterDenominator otherParameter +
    3 * parameterDenominator parameter ^ 2 * otherParameter -
    18 * parameter ^ 2 * parameterDenominator parameter *
      otherParameter ^ 2

/-- The two displayed coefficients above really are the gradient of the
tangent conic at the other parameter point, multiplied by `1+u³`. -/
theorem crossTangent_coefficients [Nontrivial K]
    (parameter otherParameter : K)
    (parameterDenominatorNonzero : parameterDenominator parameter ≠ 0)
    (otherDenominatorNonzero : parameterDenominator otherParameter ≠ 0) :
    let conic := tangentConic parameter parameterDenominatorNonzero
    let point := parameterPoint otherParameter
    parameterDenominator otherParameter *
        (conic.a + 2 * conic.d * point.x + conic.e * point.y) =
          crossTangentA parameter otherParameter ∧
      parameterDenominator otherParameter *
        (conic.b + conic.e * point.x + 2 * conic.f * point.y) =
          crossTangentB parameter otherParameter := by
  dsimp only
  let denominator := parameterDenominator otherParameter
  have cancel : denominator * denominator⁻¹ = (1 : K) :=
    RFAP.ExplicitField.mul_inv_cancel denominator otherDenominatorNonzero
  unfold tangentConic parameterPoint
  simp only [RFAP.ExplicitField.div_eq_mul_inv]
  change
    denominator *
          (9 * parameter ^ 2 +
            2 * (3 * parameter * parameterDenominator parameter) *
              ((-3 * otherParameter) * denominator⁻¹) +
            (-(parameterDenominator parameter ^ 2)) *
              ((-3 * otherParameter ^ 2) * denominator⁻¹)) =
        crossTangentA parameter otherParameter ∧
      denominator *
          (9 * parameter ^ 4 +
            (-(parameterDenominator parameter ^ 2)) *
              ((-3 * otherParameter) * denominator⁻¹) +
            2 * (3 * parameter ^ 2 * parameterDenominator parameter) *
              ((-3 * otherParameter ^ 2) * denominator⁻¹)) =
        crossTangentB parameter otherParameter
  constructor
  · calc
      denominator *
            (9 * parameter ^ 2 +
              2 * (3 * parameter * parameterDenominator parameter) *
                ((-3 * otherParameter) * denominator⁻¹) +
              (-(parameterDenominator parameter ^ 2)) *
                ((-3 * otherParameter ^ 2) * denominator⁻¹)) =
          9 * parameter ^ 2 * denominator -
            18 * parameter * parameterDenominator parameter *
              otherParameter * (denominator * denominator⁻¹) +
            3 * parameterDenominator parameter ^ 2 *
              otherParameter ^ 2 * (denominator * denominator⁻¹) := by
        ring1
      _ = crossTangentA parameter otherParameter := by
        rw [cancel]
        unfold crossTangentA
        ring1
  · calc
      denominator *
            (9 * parameter ^ 4 +
              (-(parameterDenominator parameter ^ 2)) *
                ((-3 * otherParameter) * denominator⁻¹) +
              2 * (3 * parameter ^ 2 * parameterDenominator parameter) *
                ((-3 * otherParameter ^ 2) * denominator⁻¹)) =
          9 * parameter ^ 4 * denominator +
            3 * parameterDenominator parameter ^ 2 * otherParameter *
              (denominator * denominator⁻¹) -
            18 * parameter ^ 2 * parameterDenominator parameter *
              otherParameter ^ 2 * (denominator * denominator⁻¹) := by
        ring1
      _ = crossTangentB parameter otherParameter := by
        rw [cancel]
        unfold crossTangentB
        ring1

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

/-- A line carrying only the denominator-cleared cross-tangent direction.
Its constant is irrelevant to spread. -/
def crossTangentDirection [DecidableEq K]
    (parameter otherParameter : K)
    (nonNull : crossTangentA parameter otherParameter ^ 2 +
      crossTangentB parameter otherParameter ^ 2 ≠ 0) : Line K where
  a := crossTangentA parameter otherParameter
  b := crossTangentB parameter otherParameter
  c := 0
  direction_nonzero := direction_nonzero_of_norm_nonzero nonNull

private theorem crossTangentDirection_nonNull [DecidableEq K]
    (parameter otherParameter : K)
    (nonNull : crossTangentA parameter otherParameter ^ 2 +
      crossTangentB parameter otherParameter ^ 2 ≠ 0) :
    ¬ (crossTangentDirection parameter otherParameter nonNull).IsNull := by
  unfold crossTangentDirection Line.IsNull
  exact nonNull

/-- Swap the two direction coordinates.  Simultaneously swapping both lines
does not change spread. -/
private def swapDirection (line : Line K) : Line K where
  a := line.b
  b := line.a
  c := 0
  direction_nonzero := line.direction_nonzero.elim Or.inr Or.inl

private theorem swapDirection_nonNull (line : Line K)
    (nonNull : ¬ line.IsNull) : ¬ (swapDirection line).IsNull := by
  unfold Line.IsNull at nonNull
  unfold swapDirection Line.IsNull
  intro swappedNull
  apply nonNull
  calc
    line.a ^ 2 + line.b ^ 2 = line.b ^ 2 + line.a ^ 2 := by ring1
    _ = 0 := swappedNull

private theorem spread_swapDirection
    (first second : Line K)
    (firstNonNull : ¬ first.IsNull) (secondNonNull : ¬ second.IsNull) :
    spread first second firstNonNull secondNonNull =
      spread (swapDirection first) (swapDirection second)
        (swapDirection_nonNull first firstNonNull)
        (swapDirection_nonNull second secondNonNull) := by
  unfold spread swapDirection lineNorm
  congr 1 <;> ring1

private theorem reciprocal_tangentLine_scaled [Nontrivial K]
    [DecidableEq K]
    (parameter reciprocalParameter : K) (threeNonzero : (3 : K) ≠ 0)
    (productOne : parameter * reciprocalParameter = 1) :
    parameter ^ 4 * (tangentLine reciprocalParameter threeNonzero).a =
        (tangentLine parameter threeNonzero).b ∧
      parameter ^ 4 * (tangentLine reciprocalParameter threeNonzero).b =
        (tangentLine parameter threeNonzero).a := by
  unfold tangentLine
  constructor
  · calc
      parameter ^ 4 * (reciprocalParameter *
          (2 - reciprocalParameter ^ 3)) =
        2 * parameter ^ 3 * (parameter * reciprocalParameter) -
          (parameter * reciprocalParameter) ^ 4 := by ring1
      _ = 2 * parameter ^ 3 - 1 := by rw [productOne]; ring1
  · calc
      parameter ^ 4 * (2 * reciprocalParameter ^ 3 - 1) =
          2 * parameter * (parameter * reciprocalParameter) ^ 3 -
            parameter ^ 4 := by ring1
      _ = parameter * (2 - parameter ^ 3) := by rw [productOne]; ring1

private theorem reciprocal_crossTangent_scaled
    (parameter reciprocalParameter : K)
    (productOne : parameter * reciprocalParameter = 1) :
    parameter ^ 3 * crossTangentA reciprocalParameter parameter =
      crossTangentB parameter reciprocalParameter := by
  let common :=
    3 * reciprocalParameter + 9 * parameter + 6 * parameter ^ 2 -
      18 * parameter ^ 3 + 9 * parameter ^ 4 + 3 * parameter ^ 5 - 18
  calc
    parameter ^ 3 * crossTangentA reciprocalParameter parameter =
        9 * parameter * (parameter * reciprocalParameter) ^ 2 +
          9 * parameter ^ 4 * (parameter * reciprocalParameter) ^ 2 -
          18 * parameter ^ 3 * (parameter * reciprocalParameter) -
          18 * (parameter * reciprocalParameter) ^ 4 +
          3 * parameter ^ 5 +
          6 * parameter ^ 2 * (parameter * reciprocalParameter) ^ 3 +
          3 * reciprocalParameter *
            (parameter * reciprocalParameter) ^ 5 := by
      unfold crossTangentA parameterDenominator
      ring1
    _ = common := by rw [productOne]; unfold common; ring1
    _ = 9 * parameter ^ 4 +
          9 * parameter * (parameter * reciprocalParameter) ^ 3 +
          3 * reciprocalParameter +
          6 * parameter ^ 2 * (parameter * reciprocalParameter) +
          3 * parameter ^ 5 * (parameter * reciprocalParameter) -
          18 * (parameter * reciprocalParameter) ^ 2 -
          18 * parameter ^ 3 *
            (parameter * reciprocalParameter) ^ 2 := by
      rw [productOne]
      unfold common
      ring1
    _ = crossTangentB parameter reciprocalParameter := by
      unfold crossTangentB parameterDenominator
      ring1

/-- Exercise 19.4, second assertion.  Under reciprocal parameters, the
spread between the folium tangent and the cross-tangent to its tangent conic
is the same at the two points.  The four non-null hypotheses are precisely
the finite conditions needed for the two spreads to be defined. -/
theorem reciprocal_tangent_spreads [Nontrivial K] [DecidableEq K]
    (parameter reciprocalParameter : K) (threeNonzero : (3 : K) ≠ 0)
    (productOne : parameter * reciprocalParameter = 1)
    (parameterTangentNonNull :
      ¬ (tangentLine parameter threeNonzero).IsNull)
    (reciprocalTangentNonNull :
      ¬ (tangentLine reciprocalParameter threeNonzero).IsNull)
    (parameterCrossNonNull :
      crossTangentA parameter reciprocalParameter ^ 2 +
        crossTangentB parameter reciprocalParameter ^ 2 ≠ 0)
    (reciprocalCrossNonNull :
      crossTangentA reciprocalParameter parameter ^ 2 +
        crossTangentB reciprocalParameter parameter ^ 2 ≠ 0) :
    spread (tangentLine parameter threeNonzero)
        (crossTangentDirection parameter reciprocalParameter
          parameterCrossNonNull)
        parameterTangentNonNull
        (crossTangentDirection_nonNull parameter reciprocalParameter
          parameterCrossNonNull) =
      spread (tangentLine reciprocalParameter threeNonzero)
        (crossTangentDirection reciprocalParameter parameter
          reciprocalCrossNonNull)
        reciprocalTangentNonNull
        (crossTangentDirection_nonNull reciprocalParameter parameter
          reciprocalCrossNonNull) := by
  let first := tangentLine parameter threeNonzero
  let second := crossTangentDirection parameter reciprocalParameter
    parameterCrossNonNull
  let reciprocalFirst := tangentLine reciprocalParameter threeNonzero
  let reciprocalSecond := crossTangentDirection reciprocalParameter parameter
    reciprocalCrossNonNull
  have firstScaled := reciprocal_tangentLine_scaled parameter
    reciprocalParameter threeNonzero productOne
  have crossFirstScaled := reciprocal_crossTangent_scaled parameter
    reciprocalParameter productOne
  have reverseProduct : reciprocalParameter * parameter = 1 := by
    calc
      reciprocalParameter * parameter = parameter * reciprocalParameter := by
        ring1
      _ = 1 := productOne
  have reverseCrossScaled := reciprocal_crossTangent_scaled
    reciprocalParameter parameter reverseProduct
  have crossSecondScaled :
      parameter ^ 3 * crossTangentB reciprocalParameter parameter =
        crossTangentA parameter reciprocalParameter := by
    calc
      parameter ^ 3 * crossTangentB reciprocalParameter parameter =
          parameter ^ 3 *
            (reciprocalParameter ^ 3 *
              crossTangentA parameter reciprocalParameter) := by
        rw [reverseCrossScaled]
      _ = (parameter * reciprocalParameter) ^ 3 *
          crossTangentA parameter reciprocalParameter := by ring1
      _ = crossTangentA parameter reciprocalParameter := by
        rw [productOne]
        ring1
  have firstParallel : reciprocalFirst.Parallel (swapDirection first) := by
    unfold Line.Parallel reciprocalFirst first swapDirection
    change
      (tangentLine reciprocalParameter threeNonzero).a *
          (tangentLine parameter threeNonzero).a -
        (tangentLine parameter threeNonzero).b *
          (tangentLine reciprocalParameter threeNonzero).b = 0
    rw [← firstScaled.1, ← firstScaled.2]
    ring1
  have secondParallel : reciprocalSecond.Parallel (swapDirection second) := by
    unfold Line.Parallel reciprocalSecond second swapDirection
      crossTangentDirection
    change
      crossTangentA reciprocalParameter parameter *
          crossTangentA parameter reciprocalParameter -
        crossTangentB parameter reciprocalParameter *
          crossTangentB reciprocalParameter parameter = 0
    rw [← crossFirstScaled, ← crossSecondScaled]
    ring1
  have swappedSpread := spread_swapDirection first second
    parameterTangentNonNull
    (crossTangentDirection_nonNull parameter reciprocalParameter
      parameterCrossNonNull)
  have reciprocalSpread := spread_eq_of_parallel_pairs reciprocalFirst
    reciprocalSecond (swapDirection first) (swapDirection second)
    reciprocalTangentNonNull
    (crossTangentDirection_nonNull reciprocalParameter parameter
      reciprocalCrossNonNull)
    (swapDirection_nonNull first parameterTangentNonNull)
    (swapDirection_nonNull second
      (crossTangentDirection_nonNull parameter reciprocalParameter
        parameterCrossNonNull))
    firstParallel secondParallel
  exact swappedSpread.trans reciprocalSpread.symm

end Folium

end DivineProportions
