import CCL.Riemann.ExplicitQuarticPreparedData

/-!
# Exact local certificates for the prepared cyclic quartic

The first outer cell of the canonical connector from `-1` to `1` runs along
the horizontal line `im z = -1/2`, from `-5/4` to `-1`.  This file records
the nine endpoints of its depth-three dyadic subdivision and caches the exact
values of `z^4 - 1` there as reduced constructive rationals.

Storing the reduced representatives, including their explicit Bezout
certificates, is important for the later prepared-sheet checks: direct box
clearance can inspect these small values instead of repeatedly normalizing the
large rational expression obtained by polynomial evaluation.
-/

namespace CCL.Riemann.ExplicitQuarticBranches

abbrev Q := RFAP.ConstructiveFraction.Rational

@[simp] private theorem pointReal (x y : Q) : (point x y).re = x := rfl

@[simp] private theorem pointImaginary (x y : Q) : (point x y).im = y := rfl

private theorem qNatPositive (n : Nat) (positive : 0 < n) :
    (0 : Q) < n :=
  RFAP.ConstructiveFraction.natCast_pos_direct positive

private theorem qNatNonnegative (n : Nat) : (0 : Q) ≤ n :=
  RFAP.ConstructiveFraction.natCast_le_direct (Nat.zero_le n)

private def reducedRational (num : Int) (den : Nat) (denPositive : 0 < den)
    (left right : Int)
    (bezout : left * (num.natAbs : Int) + right * (den : Int) = 1) : Q where
  num := num
  den := den
  den_pos := denPositive
  reduced := ⟨⟨left, right, bezout⟩⟩

private theorem reducedRational_eq_div (num : Int) (den : Nat)
    (denPositive : 0 < den) (left right : Int)
    (bezout : left * (num.natAbs : Int) + right * (den : Int) = 1) :
    reducedRational num den denPositive left right bezout =
      (num : Q) / (den : Q) := by
  let value := reducedRational num den denPositive left right bezout
  have denominatorPositive : (0 : Q) < den := qNatPositive den denPositive
  apply RFAP.ConstructiveFraction.mul_right_cancel_of_ne
    denominatorPositive.ne'
  calc
    value * (den : Q) = (num : Q) := by
      exact RFAP.ConstructiveFraction.representative_mul_den value
    _ = ((num : Q) / (den : Q)) * (den : Q) :=
      (RFAP.ConstructiveFraction.div_mul_cancel_of_ne _ _
        denominatorPositive.ne').symm

private theorem divEqOfNatDenominators
    {left right : Q} {leftDenominator rightDenominator : Nat}
    (leftPositive : 0 < leftDenominator)
    (rightPositive : 0 < rightDenominator)
    (cross : left * (rightDenominator : Q) =
      right * (leftDenominator : Q)) :
    left / (leftDenominator : Q) = right / (rightDenominator : Q) := by
  exact RFAP.ConstructiveFraction.div_eq_div_of_cross_mul
    (qNatPositive leftDenominator leftPositive).ne'
    (qNatPositive rightDenominator rightPositive).ne' cross

private theorem divLeDivOfCrossMul
    {leftNumerator leftDenominator rightNumerator rightDenominator : Q}
    (leftPositive : 0 < leftDenominator)
    (rightPositive : 0 < rightDenominator)
    (cross : leftNumerator * rightDenominator ≤
      rightNumerator * leftDenominator) :
    leftNumerator / leftDenominator ≤
      rightNumerator / rightDenominator := by
  apply RFAP.ConstructiveFraction.le_of_mul_le_mul_right_direct
    (c := leftDenominator * rightDenominator) _
    (RFAP.ConstructiveFraction.mul_pos_direct leftPositive rightPositive)
  calc
    leftNumerator / leftDenominator *
        (leftDenominator * rightDenominator) =
      (leftNumerator / leftDenominator * leftDenominator) *
        rightDenominator := by ring1
    _ = leftNumerator * rightDenominator := by
      rw [RFAP.ConstructiveFraction.div_mul_cancel_of_ne _ _
        leftPositive.ne']
    _ ≤ rightNumerator * leftDenominator := cross
    _ = (rightNumerator / rightDenominator * rightDenominator) *
        leftDenominator := by
      rw [RFAP.ConstructiveFraction.div_mul_cancel_of_ne _ _
        rightPositive.ne']
    _ = rightNumerator / rightDenominator *
        (leftDenominator * rightDenominator) := by ring1

private theorem addSameDenominator (left right denominator : Q)
    (nonzero : denominator ≠ 0) :
    left / denominator + right / denominator =
      (left + right) / denominator := by
  apply RFAP.ConstructiveFraction.mul_right_cancel_of_ne nonzero
  calc
    (left / denominator + right / denominator) * denominator =
        (left / denominator) * denominator +
          (right / denominator) * denominator := by ring1
    _ = left + right := by
      rw [RFAP.ConstructiveFraction.div_mul_cancel_of_ne _ _ nonzero,
        RFAP.ConstructiveFraction.div_mul_cancel_of_ne _ _ nonzero]
    _ = ((left + right) / denominator) * denominator :=
      (RFAP.ConstructiveFraction.div_mul_cancel_of_ne _ _ nonzero).symm

private theorem divMul (left denominator right : Q) :
    (left / denominator) * right = (left * right) / denominator := by
  simp only [RFAP.ConstructiveFraction.div_eq_mul_inv_direct]
  ring1

private theorem subSameDenominator (left right denominator : Q)
    (nonzero : denominator ≠ 0) :
    left / denominator - right / denominator =
      (left - right) / denominator := by
  apply RFAP.ConstructiveFraction.mul_right_cancel_of_ne nonzero
  calc
    (left / denominator - right / denominator) * denominator =
        (left / denominator) * denominator -
          (right / denominator) * denominator := by ring1
    _ = left - right := by
      rw [RFAP.ConstructiveFraction.div_mul_cancel_of_ne _ _ nonzero,
        RFAP.ConstructiveFraction.div_mul_cancel_of_ne _ _ nonzero]
    _ = ((left - right) / denominator) * denominator :=
      (RFAP.ConstructiveFraction.div_mul_cancel_of_ne _ _ nonzero).symm

private theorem quarticGridReal (n : Q) :
    ((n / 32) ^ 2 - 1 / 4) ^ 2 - (n / 32) ^ 2 - 1 =
      (n ^ 4 - 1536 * n ^ 2 - 983040) / 1048576 := by
  have thirtyTwoNe := (qNatPositive 32 (by omega)).ne'
  have oneThousandTwentyFourNe := (qNatPositive 1024 (by omega)).ne'
  have oneMillionNe := (qNatPositive 1048576 (by omega)).ne'
  have uSquare : (n / 32) ^ 2 = n ^ 2 / 1024 := by
    rw [pow_two, RFAP.ConstructiveFraction.div_mul_div_direct]
    apply RFAP.ConstructiveFraction.div_eq_div_of_cross_mul
      (RFAP.ConstructiveFraction.mul_ne_zero_direct thirtyTwoNe thirtyTwoNe)
      oneThousandTwentyFourNe
    ring1
  have quarterCommon : (1 / 4 : Q) = 256 / 1024 := by
    apply RFAP.ConstructiveFraction.div_eq_div_of_cross_mul
      (qNatPositive 4 (by omega)).ne' oneThousandTwentyFourNe
    ring1
  have difference : (n / 32) ^ 2 - 1 / 4 =
      (n ^ 2 - 256) / 1024 := by
    rw [uSquare, quarterCommon,
      subSameDenominator (n ^ 2) 256 1024 oneThousandTwentyFourNe]
  have differenceSquare : ((n ^ 2 - 256) / 1024) ^ 2 =
      (n ^ 2 - 256) ^ 2 / 1048576 := by
    rw [pow_two, RFAP.ConstructiveFraction.div_mul_div_direct]
    apply RFAP.ConstructiveFraction.div_eq_div_of_cross_mul
      (RFAP.ConstructiveFraction.mul_ne_zero_direct
        oneThousandTwentyFourNe oneThousandTwentyFourNe)
      oneMillionNe
    ring1
  have uSquareCommon : n ^ 2 / 1024 =
      (1024 * n ^ 2) / 1048576 := by
    apply RFAP.ConstructiveFraction.div_eq_div_of_cross_mul
      oneThousandTwentyFourNe oneMillionNe
    ring1
  have oneCommon : (1 : Q) = 1048576 / 1048576 := by
    apply RFAP.ConstructiveFraction.mul_right_cancel_of_ne oneMillionNe
    rw [RFAP.ConstructiveFraction.one_mul]
    exact (RFAP.ConstructiveFraction.div_mul_cancel_of_ne _ _
      oneMillionNe).symm
  rw [difference, differenceSquare, uSquare, uSquareCommon, oneCommon]
  rw [subSameDenominator ((n ^ 2 - 256) ^ 2) (1024 * n ^ 2)
    1048576 oneMillionNe]
  rw [subSameDenominator
    ((n ^ 2 - 256) ^ 2 - 1024 * n ^ 2) 1048576
      1048576 oneMillionNe]
  congr 1
  ring1

private theorem quarticGridImaginary (n : Q) :
    2 * (n / 32) * ((n / 32) ^ 2 - 1 / 4) =
      (n ^ 3 - 256 * n) / 16384 := by
  have thirtyTwoNe := (qNatPositive 32 (by omega)).ne'
  have oneThousandTwentyFourNe := (qNatPositive 1024 (by omega)).ne'
  have sixteenThousandNe := (qNatPositive 16384 (by omega)).ne'
  have thirtyTwoThousandNe := (qNatPositive 32768 (by omega)).ne'
  have uSquare : (n / 32) ^ 2 = n ^ 2 / 1024 := by
    rw [pow_two, RFAP.ConstructiveFraction.div_mul_div_direct]
    apply RFAP.ConstructiveFraction.div_eq_div_of_cross_mul
      (RFAP.ConstructiveFraction.mul_ne_zero_direct thirtyTwoNe thirtyTwoNe)
      oneThousandTwentyFourNe
    ring1
  have quarterCommon : (1 / 4 : Q) = 256 / 1024 := by
    apply RFAP.ConstructiveFraction.div_eq_div_of_cross_mul
      (qNatPositive 4 (by omega)).ne' oneThousandTwentyFourNe
    ring1
  have difference : (n / 32) ^ 2 - 1 / 4 =
      (n ^ 2 - 256) / 1024 := by
    rw [uSquare, quarterCommon,
      subSameDenominator (n ^ 2) 256 1024 oneThousandTwentyFourNe]
  rw [difference]
  have product : (n / 32) * ((n ^ 2 - 256) / 1024) =
      (n * (n ^ 2 - 256)) / 32768 := by
    rw [RFAP.ConstructiveFraction.div_mul_div_direct]
    apply RFAP.ConstructiveFraction.div_eq_div_of_cross_mul
      (RFAP.ConstructiveFraction.mul_ne_zero_direct thirtyTwoNe
        oneThousandTwentyFourNe) thirtyTwoThousandNe
    ring1
  rw [show (2 : Q) * (n / 32) * ((n ^ 2 - 256) / 1024) =
    2 * ((n / 32) * ((n ^ 2 - 256) / 1024)) by ring1, product]
  change 2 * ((n * (n ^ 2 - 256)) / 32768) = _
  have asFraction : 2 * ((n * (n ^ 2 - 256)) / 32768) =
      (2 * (n * (n ^ 2 - 256))) / 32768 := by
    simp only [RFAP.ConstructiveFraction.div_eq_mul_inv_direct]
    ring1
  rw [asFraction]
  apply RFAP.ConstructiveFraction.div_eq_div_of_cross_mul
    thirtyTwoThousandNe sixteenThousandNe
  ring1

/-- Exact symbolic value of `z^4 - 1` on the dyadic horizontal grid used by
the first prepared connector cell. -/
theorem quarticGridEvaluation (n : Q) :
    CCL.Riemann.FinitePeriodExamples.quarticPolynomial.eval
        (point (-(n / 32)) (-1 / 2)) =
      point ((n ^ 4 - 1536 * n ^ 2 - 983040) / 1048576)
        ((n ^ 3 - 256 * n) / 16384) := by
  unfold CCL.Riemann.FinitePeriodExamples.quarticPolynomial
  rw [CCL.PowerMonodromy.polynomial_eval]
  unfold CCL.Riemann.FinitePeriodExamples.degreeFour
  have halfSquare : (-1 / 2 : Q) ^ 2 = 1 / 4 := by
    with_unfolding_all decide
  have negHalfPlusNegHalf : (-1 / 2 : Q) + (-1 / 2) = -1 := by
    with_unfolding_all decide
  have firstSquare : point (-(n / 32)) (-1 / 2) ^ 2 =
      point ((n / 32) ^ 2 - 1 / 4) (n / 32) := by
    rw [pow_two]
    apply RFAP.ConstructiveGaussian.Gaussian.ext
    · simp only [RFAP.ConstructiveGaussian.Gaussian.mul_re,
        pointReal, pointImaginary]
      calc
        (-(n / 32)) * (-(n / 32)) - (-1 / 2) * (-1 / 2) =
            (n / 32) ^ 2 - (-1 / 2) ^ 2 := by ring1
        _ = (n / 32) ^ 2 - 1 / 4 := by rw [halfSquare]
    · simp only [RFAP.ConstructiveGaussian.Gaussian.mul_im,
        pointReal, pointImaginary]
      calc
        (-(n / 32)) * (-1 / 2) + (-1 / 2) * (-(n / 32)) =
            (-(n / 32)) * ((-1 / 2) + (-1 / 2)) := by ring1
        _ = (-(n / 32)) * (-1) := by rw [negHalfPlusNegHalf]
        _ = n / 32 := by ring1
  rw [show point (-(n / 32)) (-1 / 2) ^ 4 =
    (point (-(n / 32)) (-1 / 2) ^ 2) ^ 2 by ring1, firstSquare, pow_two]
  apply RFAP.ConstructiveGaussian.Gaussian.ext
  · simp only [RFAP.ConstructiveGaussian.Gaussian.mul_re,
      RFAP.ConstructiveGaussian.Gaussian.sub_re,
      RFAP.ConstructiveGaussian.Gaussian.one_re,
      pointReal, pointImaginary]
    simpa only [pow_two] using quarticGridReal n
  · simp only [RFAP.ConstructiveGaussian.Gaussian.mul_im,
      RFAP.ConstructiveGaussian.Gaussian.sub_im,
      RFAP.ConstructiveGaussian.Gaussian.one_im,
      pointReal, pointImaginary]
    calc
      ((n / 32) ^ 2 - 1 / 4) * (n / 32) +
          (n / 32) * ((n / 32) ^ 2 - 1 / 4) - 0 =
        2 * (n / 32) * ((n / 32) ^ 2 - 1 / 4) := by ring1
      _ = (n ^ 3 - 256 * n) / 16384 := quarticGridImaginary n

private theorem finNineCases (index : Fin 9) :
    index = 0 ∨ index = 1 ∨ index = 2 ∨ index = 3 ∨ index = 4 ∨
      index = 5 ∨ index = 6 ∨ index = 7 ∨ index = 8 := by
  rcases index with ⟨value, bound⟩
  omega0

/-- The nine input endpoints of the depth-three subdivision of the first
outer connector cell. -/
def firstConnectorGridInput : Fin 9 → Gaussian
  | ⟨0, _⟩ => point (-(40 / 32)) (-1 / 2)
  | ⟨1, _⟩ => point (-(39 / 32)) (-1 / 2)
  | ⟨2, _⟩ => point (-(38 / 32)) (-1 / 2)
  | ⟨3, _⟩ => point (-(37 / 32)) (-1 / 2)
  | ⟨4, _⟩ => point (-(36 / 32)) (-1 / 2)
  | ⟨5, _⟩ => point (-(35 / 32)) (-1 / 2)
  | ⟨6, _⟩ => point (-(34 / 32)) (-1 / 2)
  | ⟨7, _⟩ => point (-(33 / 32)) (-1 / 2)
  | ⟨8, _⟩ => point (-(32 / 32)) (-1 / 2)

/-- Cached reduced values of `z^4 - 1` at `firstConnectorGridInput`.
Every coordinate includes a kernel-checkable Bezout certificate for the
stored numerator and denominator. -/
def firstConnectorGridParameter : Fin 9 → Gaussian
  | ⟨0, _⟩ => point
      (reducedRational (-215) 256 (by omega) (-25) 21 (by omega))
      (reducedRational 105 32 (by omega) (-7) 23 (by omega))
  | ⟨1, _⟩ => point
      (reducedRational (-1005855) 1048576 (by omega)
        (-204065) 195751 (by omega))
      (reducedRational 49335 16384 (by omega) 7431 (-22376) (by omega))
  | ⟨2, _⟩ => point
      (reducedRational (-69743) 65536 (by omega) 20111 (-21402) (by omega))
      (reducedRational 5643 2048 (by omega) (-605) 1667 (by omega))
  | ⟨3, _⟩ => point
      (reducedRational (-1211663) 1048576 (by omega)
        (-208401) 240814 (by omega))
      (reducedRational 41181 16384 (by omega) (-2187) 5497 (by omega))
  | ⟨4, _⟩ => point
      (reducedRational (-5055) 4096 (by omega) (-961) 1186 (by omega))
      (reducedRational 585 256 (by omega) (-7) 16 (by omega))
  | ⟨5, _⟩ => point
      (reducedRational (-1364015) 1048576 (by omega)
        (-362801) 471941 (by omega))
      (reducedRational 33915 16384 (by omega) (-1357) 2809 (by omega))
  | ⟨6, _⟩ => point
      (reducedRational (-88895) 65536 (by omega) 5311 (-7204) (by omega))
      (reducedRational 3825 2048 (by omega) 529 (-988) (by omega))
  | ⟨7, _⟩ => point
      (reducedRational (-1469823) 1048576 (by omega)
        217727 (-305195) (by omega))
      (reducedRational 27489 16384 (by omega) (-1887) 3166 (by omega))
  | ⟨8, _⟩ => point
      (reducedRational (-23) 16 (by omega) 7 (-10) (by omega))
      (reducedRational 3 2 (by omega) 1 (-1) (by omega))

/-- The cached parameter table agrees exactly with polynomial evaluation. -/
theorem quarticPolynomial_eval_firstConnectorGridInput (index : Fin 9) :
    CCL.Riemann.FinitePeriodExamples.quarticPolynomial.eval
        (firstConnectorGridInput index) =
      firstConnectorGridParameter index := by
  rcases finNineCases index with h | h | h | h | h | h | h | h | h
  · subst index
    simp only [firstConnectorGridInput, firstConnectorGridParameter]
    rw [quarticGridEvaluation]
    simp only [reducedRational_eq_div]
    apply RFAP.ConstructiveGaussian.Gaussian.ext
    · apply divEqOfNatDenominators
        (leftDenominator := 1048576) (rightDenominator := 256) <;>
        first | omega | ring1
    · apply divEqOfNatDenominators
        (leftDenominator := 16384) (rightDenominator := 32) <;>
        first | omega | ring1
  · subst index
    simp only [firstConnectorGridInput, firstConnectorGridParameter]
    rw [quarticGridEvaluation]
    simp only [reducedRational_eq_div]
    apply RFAP.ConstructiveGaussian.Gaussian.ext
    · apply divEqOfNatDenominators
        (leftDenominator := 1048576) (rightDenominator := 1048576) <;>
        first | omega | ring1
    · apply divEqOfNatDenominators
        (leftDenominator := 16384) (rightDenominator := 16384) <;>
        first | omega | ring1
  · subst index
    simp only [firstConnectorGridInput, firstConnectorGridParameter]
    rw [quarticGridEvaluation]
    simp only [reducedRational_eq_div]
    apply RFAP.ConstructiveGaussian.Gaussian.ext
    · apply divEqOfNatDenominators
        (leftDenominator := 1048576) (rightDenominator := 65536) <;>
        first | omega | ring1
    · apply divEqOfNatDenominators
        (leftDenominator := 16384) (rightDenominator := 2048) <;>
        first | omega | ring1
  · subst index
    simp only [firstConnectorGridInput, firstConnectorGridParameter]
    rw [quarticGridEvaluation]
    simp only [reducedRational_eq_div]
    apply RFAP.ConstructiveGaussian.Gaussian.ext
    · apply divEqOfNatDenominators
        (leftDenominator := 1048576) (rightDenominator := 1048576) <;>
        first | omega | ring1
    · apply divEqOfNatDenominators
        (leftDenominator := 16384) (rightDenominator := 16384) <;>
        first | omega | ring1
  · subst index
    simp only [firstConnectorGridInput, firstConnectorGridParameter]
    rw [quarticGridEvaluation]
    simp only [reducedRational_eq_div]
    apply RFAP.ConstructiveGaussian.Gaussian.ext
    · apply divEqOfNatDenominators
        (leftDenominator := 1048576) (rightDenominator := 4096) <;>
        first | omega | ring1
    · apply divEqOfNatDenominators
        (leftDenominator := 16384) (rightDenominator := 256) <;>
        first | omega | ring1
  · subst index
    simp only [firstConnectorGridInput, firstConnectorGridParameter]
    rw [quarticGridEvaluation]
    simp only [reducedRational_eq_div]
    apply RFAP.ConstructiveGaussian.Gaussian.ext
    · apply divEqOfNatDenominators
        (leftDenominator := 1048576) (rightDenominator := 1048576) <;>
        first | omega | ring1
    · apply divEqOfNatDenominators
        (leftDenominator := 16384) (rightDenominator := 16384) <;>
        first | omega | ring1
  · subst index
    simp only [firstConnectorGridInput, firstConnectorGridParameter]
    rw [quarticGridEvaluation]
    simp only [reducedRational_eq_div]
    apply RFAP.ConstructiveGaussian.Gaussian.ext
    · apply divEqOfNatDenominators
        (leftDenominator := 1048576) (rightDenominator := 65536) <;>
        first | omega | ring1
    · apply divEqOfNatDenominators
        (leftDenominator := 16384) (rightDenominator := 2048) <;>
        first | omega | ring1
  · subst index
    simp only [firstConnectorGridInput, firstConnectorGridParameter]
    rw [quarticGridEvaluation]
    simp only [reducedRational_eq_div]
    apply RFAP.ConstructiveGaussian.Gaussian.ext
    · apply divEqOfNatDenominators
        (leftDenominator := 1048576) (rightDenominator := 1048576) <;>
        first | omega | ring1
    · apply divEqOfNatDenominators
        (leftDenominator := 16384) (rightDenominator := 16384) <;>
        first | omega | ring1
  · subst index
    simp only [firstConnectorGridInput, firstConnectorGridParameter]
    rw [quarticGridEvaluation]
    simp only [reducedRational_eq_div]
    apply RFAP.ConstructiveGaussian.Gaussian.ext
    · apply divEqOfNatDenominators
        (leftDenominator := 1048576) (rightDenominator := 16) <;>
        first | omega | ring1
    · apply divEqOfNatDenominators
        (leftDenominator := 16384) (rightDenominator := 2) <;>
        first | omega | ring1

/-! ## Cached direct-clearance data

The recentering steps at grid endpoints zero and four produce the two boxes
below.  The next three endpoints in each box use same-box strengthening.  We
cache both the exact direct clearance object and its common `5/8` lower bound
for those six endpoints.  This is precisely the closed endpoint needed
against the strict `40/64` variation bound.
-/

/-- The owner box used after recentering at the first grid endpoint. -/
def firstConnectorBoxOne : Box :=
  { xLower := reducedRational 17 32 (by omega) (-15) 8 (by omega)
    xUpper := reducedRational 65 32 (by omega) 1 (-2) (by omega)
    yLower := reducedRational 31 32 (by omega) (-1) 1 (by omega)
    yUpper := reducedRational 79 32 (by omega) 15 (-37) (by omega)
    x_valid := by with_unfolding_all decide
    y_valid := by with_unfolding_all decide }

/-- The owner box used after recentering at the fifth grid endpoint. -/
def firstConnectorBoxTwo : Box :=
  { xLower := reducedRational 1 4 (by omega) 1 0 (by omega)
    xUpper := reducedRational 7 4 (by omega) (-1) 2 (by omega)
    yLower := reducedRational 11 16 (by omega) 3 (-2) (by omega)
    yUpper := reducedRational 35 16 (by omega) (-5) 11 (by omega)
    x_valid := by with_unfolding_all decide
    y_valid := by with_unfolding_all decide }

/-- A cached exact boundary-clearance calculation whose four side bounds are
all at least `5/8`. -/
structure DirectClearanceFiveEighths (parameter : Gaussian) (box : Box) where
  leftNonzero :
    CCL.Riemann.SquareRootContinuationChain.Owner.verticalDeterminant
      parameter box.xLower ≠ 0
  rightNonzero :
    CCL.Riemann.SquareRootContinuationChain.Owner.verticalDeterminant
      parameter box.xUpper ≠ 0
  bottomNonzero :
    CCL.Riemann.SquareRootContinuationChain.Owner.horizontalDeterminant
      parameter box.yLower ≠ 0
  topNonzero :
    CCL.Riemann.SquareRootContinuationChain.Owner.horizontalDeterminant
      parameter box.yUpper ≠ 0
  clearance : RFAP.BoxClearance.BoundaryClearance
    (CCL.PowerMonodromy.polynomial parameter
      CCL.Riemann.SquareRootSheets.degreeTwo) box
  clearance_eq : clearance =
    CCL.Riemann.ExactQuadraticOwnerClearance.directBoundaryClearance
      parameter box leftNonzero rightNonzero bottomNonzero topNonzero
  fiveEighths_le : (5 / 8 : Q) ≤ clearance.bound
  directBound_le_threeHalves :
    min
      (CCL.Riemann.ExactQuadraticOwnerClearance.directVerticalClearanceBound
        parameter box box.xLower)
      (min
        (CCL.Riemann.ExactQuadraticOwnerClearance.directVerticalClearanceBound
          parameter box box.xUpper)
        (min
          (CCL.Riemann.ExactQuadraticOwnerClearance.directHorizontalClearanceBound
            parameter box box.yLower)
          (CCL.Riemann.ExactQuadraticOwnerClearance.directHorizontalClearanceBound
            parameter box box.yUpper))) ≤ (3 / 2 : Q)

private def directClearanceFiveEighthsOfChecks
    (parameter : Gaussian) (box : Box)
    (leftNonzero :
      CCL.Riemann.SquareRootContinuationChain.Owner.verticalDeterminant
        parameter box.xLower ≠ 0)
    (rightNonzero :
      CCL.Riemann.SquareRootContinuationChain.Owner.verticalDeterminant
        parameter box.xUpper ≠ 0)
    (bottomNonzero :
      CCL.Riemann.SquareRootContinuationChain.Owner.horizontalDeterminant
        parameter box.yLower ≠ 0)
    (topNonzero :
      CCL.Riemann.SquareRootContinuationChain.Owner.horizontalDeterminant
        parameter box.yUpper ≠ 0)
    (leftLe : (5 / 8 : Q) ≤
      CCL.Riemann.ExactQuadraticOwnerClearance.directVerticalClearanceBound
        parameter box box.xLower)
    (rightLe : (5 / 8 : Q) ≤
      CCL.Riemann.ExactQuadraticOwnerClearance.directVerticalClearanceBound
        parameter box box.xUpper)
    (bottomLe : (5 / 8 : Q) ≤
      CCL.Riemann.ExactQuadraticOwnerClearance.directHorizontalClearanceBound
        parameter box box.yLower)
    (topLe : (5 / 8 : Q) ≤
      CCL.Riemann.ExactQuadraticOwnerClearance.directHorizontalClearanceBound
        parameter box box.yUpper)
    (upper :
      min
        (CCL.Riemann.ExactQuadraticOwnerClearance.directVerticalClearanceBound
          parameter box box.xLower)
        (min
          (CCL.Riemann.ExactQuadraticOwnerClearance.directVerticalClearanceBound
            parameter box box.xUpper)
          (min
            (CCL.Riemann.ExactQuadraticOwnerClearance.directHorizontalClearanceBound
              parameter box box.yLower)
            (CCL.Riemann.ExactQuadraticOwnerClearance.directHorizontalClearanceBound
              parameter box box.yUpper))) ≤ (3 / 2 : Q)) :
    DirectClearanceFiveEighths parameter box :=
  { leftNonzero := leftNonzero
    rightNonzero := rightNonzero
    bottomNonzero := bottomNonzero
    topNonzero := topNonzero
    clearance :=
      CCL.Riemann.ExactQuadraticOwnerClearance.directBoundaryClearance
        parameter box leftNonzero rightNonzero bottomNonzero topNonzero
    clearance_eq := rfl
    fiveEighths_le :=
      CCL.Riemann.ExactQuadraticOwnerClearance.le_directBoundaryClearance_bound
        parameter box leftNonzero rightNonzero bottomNonzero topNonzero (5 / 8)
          leftLe rightLe bottomLe topLe
    directBound_le_threeHalves := upper }

/-- The three grid entries strengthened inside `firstConnectorBoxOne`. -/
def firstConnectorBoxOneIndex : Fin 3 → Fin 9
  | ⟨0, _⟩ => 1
  | ⟨1, _⟩ => 2
  | ⟨2, _⟩ => 3

/-- The three grid entries strengthened inside `firstConnectorBoxTwo`. -/
def firstConnectorBoxTwoIndex : Fin 3 → Fin 9
  | ⟨0, _⟩ => 5
  | ⟨1, _⟩ => 6
  | ⟨2, _⟩ => 7

/-- Cached direct-clearance calculations for the first strengthening run. -/
def firstConnectorBoxOneClearance : (index : Fin 3) →
    DirectClearanceFiveEighths
      (firstConnectorGridParameter (firstConnectorBoxOneIndex index))
      firstConnectorBoxOne
  | ⟨0, _⟩ => by
      apply directClearanceFiveEighthsOfChecks
      all_goals with_unfolding_all decide +revert
  | ⟨1, _⟩ => by
      apply directClearanceFiveEighthsOfChecks
      all_goals with_unfolding_all decide +revert
  | ⟨2, _⟩ => by
      apply directClearanceFiveEighthsOfChecks
      all_goals with_unfolding_all decide +revert

/-- Cached direct-clearance calculations for the second strengthening run. -/
def firstConnectorBoxTwoClearance : (index : Fin 3) →
    DirectClearanceFiveEighths
      (firstConnectorGridParameter (firstConnectorBoxTwoIndex index))
      firstConnectorBoxTwo
  | ⟨0, _⟩ => by
      apply directClearanceFiveEighthsOfChecks
      all_goals with_unfolding_all decide +revert
  | ⟨1, _⟩ => by
      apply directClearanceFiveEighthsOfChecks
      all_goals with_unfolding_all decide +revert
  | ⟨2, _⟩ => by
      apply directClearanceFiveEighthsOfChecks
      all_goals with_unfolding_all decide +revert

/-! ## Connection to the executable prepared segment -/

private structure ConnectorHeadData
    {polynomial : RFAP.ConstructivePolynomial.GaussianPolynomial}
    {ambient : RFAP.Boxes.Box}
    {start finish : RFAP.ConstructiveGaussian.Gaussian}
    (path : CCL.Riemann.BranchCuts.ClearPath polynomial ambient start finish) where
  middle : RFAP.ConstructiveGaussian.Gaussian
  head : CCL.Riemann.BranchCuts.ClearSegment polynomial ambient start middle
  tail : CCL.Riemann.BranchCuts.ClearPath polynomial ambient middle finish
  path_eq : path = .cons head tail

private def firstRawConnectorHeadData :
    ConnectorHeadData (rawConnector 0 1) := by
  unfold rawConnector CCL.Riemann.BranchCuts.finiteConnectorAt
  exact ⟨_, _, _, rfl⟩

private theorem firstRawConnectorHead_withinAmbient :
    firstRawConnectorHeadData.head.WithinAmbient := by
  have within := rawConnector_withinAmbient 0 1
  rw [firstRawConnectorHeadData.path_eq] at within
  exact within.head

/-- The first of the eight outer cells of the canonical connector from `-1`
to `1`.  Its own depth-three mesh has the nine endpoints cached above. -/
def firstConnectorSegment :=
  firstRawConnectorHeadData.head.restrict
    firstRawConnectorHead_withinAmbient 0 (1 / 8)
      (by decide) (by decide)

theorem firstConnectorSegment_withinAmbient :
    firstConnectorSegment.WithinAmbient :=
  firstRawConnectorHeadData.head.restrict_withinAmbient
    firstRawConnectorHead_withinAmbient 0 (1 / 8)
      (by decide) (by decide)

private theorem firstConnectorSegment_start_eq :
    firstRawConnectorHeadData.head.pointAt 0 =
      point (-5 / 4) (-1 / 2) := by
  with_unfolding_all rfl

private theorem firstConnectorSegment_finish_eq :
    firstRawConnectorHeadData.head.pointAt (1 / 8) =
      point (-1) (-1 / 2) := by
  with_unfolding_all decide

/-- Affine coordinate formula for the first connector cell. -/
theorem firstConnectorSegment_pointAt (parameter : Q) :
    firstConnectorSegment.pointAt parameter =
      point ((-5 / 4) + parameter * ((-1) - (-5 / 4)))
        ((-1 / 2) + parameter * ((-1 / 2) - (-1 / 2))) := by
  change firstRawConnectorHeadData.head.pointAt 0 +
    CCL.FiniteExp.scale parameter
      (firstRawConnectorHeadData.head.pointAt (1 / 8) -
        firstRawConnectorHeadData.head.pointAt 0) = _
  rw [firstConnectorSegment_start_eq, firstConnectorSegment_finish_eq]
  apply RFAP.ConstructiveGaussian.Gaussian.ext <;>
    simp only [RFAP.ConstructiveGaussian.Gaussian.add_re,
      RFAP.ConstructiveGaussian.Gaussian.add_im,
      RFAP.ConstructiveGaussian.Gaussian.sub_re,
      RFAP.ConstructiveGaussian.Gaussian.sub_im,
      CCL.FiniteExp.scale_re, CCL.FiniteExp.scale_im,
      pointReal, pointImaginary]

private theorem firstConnectorRealAt (k n : Q) (sum : k + n = 40) :
    (-5 / 4 : Q) + (k / 8) * ((-1) - (-5 / 4)) = -(n / 32) := by
  have dx : (-1 : Q) - (-5 / 4) = 1 / 4 := by
    with_unfolding_all decide
  have product : (k / 8 : Q) * (1 / 4) = k / 32 := by
    rw [RFAP.ConstructiveFraction.div_mul_div_direct]
    apply RFAP.ConstructiveFraction.div_eq_div_of_cross_mul
      (RFAP.ConstructiveFraction.mul_ne_zero_direct
        (qNatPositive 8 (by omega)).ne' (qNatPositive 4 (by omega)).ne')
      (qNatPositive 32 (by omega)).ne'
    ring1
  have startCommon : (-5 / 4 : Q) = -40 / 32 := by
    apply RFAP.ConstructiveFraction.div_eq_div_of_cross_mul
      (qNatPositive 4 (by omega)).ne' (qNatPositive 32 (by omega)).ne'
    ring1
  rw [dx, product, startCommon]
  simp only [RFAP.ConstructiveFraction.div_eq_mul_inv_direct]
  rw [← sum]
  ring1

/-- The canonical endpoint data for the depth-three mesh of
`firstConnectorSegment`. -/
def firstConnectorGridEndpoint : Fin 9 →
    CCL.Riemann.ClearSheetContinuation.Subdivision.Endpoint
  | ⟨0, _⟩ => ⟨0 / 8, by decide⟩
  | ⟨1, _⟩ => ⟨1 / 8, by decide⟩
  | ⟨2, _⟩ => ⟨2 / 8, by decide⟩
  | ⟨3, _⟩ => ⟨3 / 8, by decide⟩
  | ⟨4, _⟩ => ⟨4 / 8, by decide⟩
  | ⟨5, _⟩ => ⟨5 / 8, by decide⟩
  | ⟨6, _⟩ => ⟨6 / 8, by decide⟩
  | ⟨7, _⟩ => ⟨7 / 8, by decide⟩
  | ⟨8, _⟩ => ⟨8 / 8, by decide⟩

/-- The same nine endpoints, with the two boundary entries definitionally
aligned to the standard complete-segment endpoints. -/
def firstConnectorMeshEndpoint : Fin 9 →
    CCL.Riemann.ClearSheetContinuation.Subdivision.Endpoint
  | ⟨0, _⟩ => CCL.Riemann.PreparedClearPathModels.zeroEndpoint
  | ⟨1, _⟩ => firstConnectorGridEndpoint 1
  | ⟨2, _⟩ => firstConnectorGridEndpoint 2
  | ⟨3, _⟩ => firstConnectorGridEndpoint 3
  | ⟨4, _⟩ => firstConnectorGridEndpoint 4
  | ⟨5, _⟩ => firstConnectorGridEndpoint 5
  | ⟨6, _⟩ => firstConnectorGridEndpoint 6
  | ⟨7, _⟩ => firstConnectorGridEndpoint 7
  | ⟨8, _⟩ => CCL.Riemann.PreparedClearPathModels.oneEndpoint

/-- `firstConnectorMeshEndpoint` changes only proof-level boundary
presentations; its rational parameters are the exact cached grid parameters. -/
theorem firstConnectorMeshEndpoint_parameter (index : Fin 9) :
    (firstConnectorMeshEndpoint index).parameter =
      (firstConnectorGridEndpoint index).parameter := by
  rcases finNineCases index with h | h | h | h | h | h | h | h | h
  all_goals (subst index; rfl)

/-- The abstract mesh endpoint is exactly the corresponding cached input. -/
theorem firstConnectorSegment_pointAt_gridEndpoint (index : Fin 9) :
    firstConnectorSegment.pointAt
      (firstConnectorGridEndpoint index).parameter =
        firstConnectorGridInput index := by
  rcases finNineCases index with h | h | h | h | h | h | h | h | h
  all_goals subst index
  all_goals rw [firstConnectorSegment_pointAt]
  all_goals apply RFAP.ConstructiveGaussian.Gaussian.ext
  all_goals simp only [firstConnectorGridEndpoint,
    firstConnectorGridInput, pointReal, pointImaginary]
  all_goals first | (apply firstConnectorRealAt <;> ring1) | ring1

/-- Polynomial evaluation at the actual subdivision endpoint is the cached
reduced parameter value. -/
theorem quarticPolynomial_eval_firstConnectorGridEndpoint (index : Fin 9) :
    CCL.Riemann.FinitePeriodExamples.quarticPolynomial.eval
      (firstConnectorSegment.pointAt
        (firstConnectorGridEndpoint index).parameter) =
      firstConnectorGridParameter index := by
  rw [firstConnectorSegment_pointAt_gridEndpoint]
  exact quarticPolynomial_eval_firstConnectorGridInput index

/-- Polynomial evaluation at the canonically aligned mesh endpoint is the
same cached reduced parameter. -/
theorem quarticPolynomial_eval_firstConnectorMeshEndpoint (index : Fin 9) :
    CCL.Riemann.FinitePeriodExamples.quarticPolynomial.eval
      (firstConnectorSegment.pointAt
        (firstConnectorMeshEndpoint index).parameter) =
      firstConnectorGridParameter index := by
  rw [firstConnectorMeshEndpoint_parameter]
  exact quarticPolynomial_eval_firstConnectorGridEndpoint index

private theorem finEightCases (index : Fin 8) :
    index = 0 ∨ index = 1 ∨ index = 2 ∨ index = 3 ∨
      index = 4 ∨ index = 5 ∨ index = 6 ∨ index = 7 := by
  rcases index with ⟨value, bound⟩
  omega0

/-- Source endpoint of each of the eight local dyadic edges. -/
def firstConnectorEdgeSource : Fin 8 → Fin 9
  | ⟨0, _⟩ => 0
  | ⟨1, _⟩ => 1
  | ⟨2, _⟩ => 2
  | ⟨3, _⟩ => 3
  | ⟨4, _⟩ => 4
  | ⟨5, _⟩ => 5
  | ⟨6, _⟩ => 6
  | ⟨7, _⟩ => 7

/-- Target endpoint of each of the eight local dyadic edges. -/
def firstConnectorEdgeTarget : Fin 8 → Fin 9
  | ⟨0, _⟩ => 1
  | ⟨1, _⟩ => 2
  | ⟨2, _⟩ => 3
  | ⟨3, _⟩ => 4
  | ⟨4, _⟩ => 5
  | ⟨5, _⟩ => 6
  | ⟨6, _⟩ => 7
  | ⟨7, _⟩ => 8

/-- The canonical branch owner, reindexed to the start of the first outer
connector cell. -/
def firstConnectorStartOwner :=
  CCL.Riemann.PreparedClearPathModels.ownerAtStart firstConnectorSegment
    (CCL.Riemann.PreparedClearPathModels.ownerAtStart
      firstRawConnectorHeadData.head (branchSquareRootOwner 0 0))

/-- Diameter request for each edge of the first connector-cell mesh. -/
def firstConnectorEdgeRequest (edge : Fin 8) :
    CCL.Riemann.PreparedSheetContinuation.StepRequest :=
  { endpoint := firstConnectorMeshEndpoint (firstConnectorEdgeTarget edge)
    rootDiameter := workingRootDiameter
    rootDiameterPositive := workingRootDiameter_positive }

private theorem firstConnectorPoint_normSq_le (n : Nat) (bound : n ≤ 40) :
    RFAP.ConstructiveGaussian.Gaussian.normSq
      (point (-((n : Q) / 32)) (-1 / 2)) ≤ (29 / 16 : Q) := by
  have nNonnegative : (0 : Q) ≤ n := qNatNonnegative n
  have ratioNonnegative : (0 : Q) ≤ (n : Q) / 32 :=
    RFAP.ConstructiveFraction.div_nonneg_direct nNonnegative
      (qNatPositive 32 (by omega)).le
  have nLeForty : (n : Q) ≤ 40 :=
    RFAP.ConstructiveFraction.natCast_le_direct bound
  have ratioLe : ((n : Q) / 32) ≤ 5 / 4 := by
    apply divLeDivOfCrossMul
      (qNatPositive 32 (by omega)) (qNatPositive 4 (by omega))
    calc
      (n : Q) * 4 ≤ 40 * 4 :=
        RFAP.ConstructiveFraction.mul_le_mul_of_nonneg_right_direct
          nLeForty (by decide)
      _ = 5 * 32 := by ring1
  have negHalf : (-1 / 2 : Q) = -(1 / 2) := by
    simp only [RFAP.ConstructiveFraction.div_eq_mul_inv_direct]
    ring1
  change (-((n : Q) / 32)) ^ 2 + (-1 / 2) ^ 2 ≤ 29 / 16
  rw [neg_sq, negHalf, neg_sq]
  calc
    ((n : Q) / 32) ^ 2 + (1 / 2 : Q) ^ 2 ≤
        (5 / 4 : Q) ^ 2 + (1 / 2 : Q) ^ 2 :=
      add_le_add
        (RFAP.ConstructiveFraction.pow_le_pow_direct
          ratioNonnegative ratioLe 2) le_rfl
    _ = 29 / 16 := by with_unfolding_all decide

/-- Every input point of the first connector cell lies in the uniform
`29/16` squared-norm disk. -/
theorem firstConnectorGridInput_normSq_le (index : Fin 9) :
    RFAP.ConstructiveGaussian.Gaussian.normSq
      (firstConnectorGridInput index) ≤ (29 / 16 : Q) := by
  rcases finNineCases index with h | h | h | h | h | h | h | h | h
  · subst index
    exact firstConnectorPoint_normSq_le 40 (by omega)
  · subst index
    exact firstConnectorPoint_normSq_le 39 (by omega)
  · subst index
    exact firstConnectorPoint_normSq_le 38 (by omega)
  · subst index
    exact firstConnectorPoint_normSq_le 37 (by omega)
  · subst index
    exact firstConnectorPoint_normSq_le 36 (by omega)
  · subst index
    exact firstConnectorPoint_normSq_le 35 (by omega)
  · subst index
    exact firstConnectorPoint_normSq_le 34 (by omega)
  · subst index
    exact firstConnectorPoint_normSq_le 33 (by omega)
  · subst index
    exact firstConnectorPoint_normSq_le 32 (by omega)

private theorem adjacentConnectorPoint_normSq (n m : Q)
    (adjacent : n = m + 1) :
    RFAP.ConstructiveGaussian.Gaussian.normSq
      (point (-(n / 32)) (-1 / 2) - point (-(m / 32)) (-1 / 2)) =
      (1 / 1024 : Q) := by
  have difference :
      point (-(n / 32)) (-1 / 2) - point (-(m / 32)) (-1 / 2) =
        point (-1 / 32) 0 := by
    apply RFAP.ConstructiveGaussian.Gaussian.ext
    · simp only [RFAP.ConstructiveGaussian.Gaussian.sub_re, point]
      simp only [RFAP.ConstructiveFraction.div_eq_mul_inv_direct]
      rw [adjacent]
      ring1
    · simp only [RFAP.ConstructiveGaussian.Gaussian.sub_im, point]
      ring1
  rw [difference]
  change (-1 / 32 : Q) ^ 2 + 0 ^ 2 = 1 / 1024
  rw [pow_two, RFAP.ConstructiveFraction.div_mul_div_direct]
  rw [show (-1 : Q) * (-1) = 1 by ring1,
    show (32 : Q) * 32 = 1024 by ring1]
  ring1

private theorem firstConnectorGridInput_adjacent_normSq (edge : Fin 8) :
    RFAP.ConstructiveGaussian.Gaussian.normSq
      (firstConnectorGridInput (firstConnectorEdgeSource edge) -
        firstConnectorGridInput (firstConnectorEdgeTarget edge)) =
      (1 / 1024 : Q) := by
  rcases finEightCases edge with h | h | h | h | h | h | h | h
  all_goals subst edge
  all_goals simp only [firstConnectorEdgeSource, firstConnectorEdgeTarget,
    firstConnectorGridInput]
  all_goals (apply adjacentConnectorPoint_normSq; ring1)

/-- Adjacent cached quartic parameters differ in squared norm by at most
`7/64`.  The proof uses `z⁴ - w⁴ = (z-w)(z+w)(z²+w²)` and uniform
finite bounds on the nine input points, avoiding expensive normalization of
the cached output fractions. -/
theorem firstConnectorGridDisplacement_le (edge : Fin 8) :
    RFAP.ConstructiveGaussian.Gaussian.normSq
      (firstConnectorGridParameter (firstConnectorEdgeSource edge) -
        firstConnectorGridParameter (firstConnectorEdgeTarget edge)) ≤
      (7 / 64 : Q) := by
  let z := firstConnectorGridInput (firstConnectorEdgeSource edge)
  let w := firstConnectorGridInput (firstConnectorEdgeTarget edge)
  have zNorm : RFAP.ConstructiveGaussian.Gaussian.normSq z ≤
      (29 / 16 : Q) :=
    firstConnectorGridInput_normSq_le (firstConnectorEdgeSource edge)
  have wNorm : RFAP.ConstructiveGaussian.Gaussian.normSq w ≤
      (29 / 16 : Q) :=
    firstConnectorGridInput_normSq_le (firstConnectorEdgeTarget edge)
  have sumNorm : RFAP.ConstructiveGaussian.Gaussian.normSq (z + w) ≤
      (29 / 4 : Q) :=
    (RFAP.ConstructiveGaussian.Gaussian.normSq_add_le_two z w).trans (by
      calc
        2 * (RFAP.ConstructiveGaussian.Gaussian.normSq z +
            RFAP.ConstructiveGaussian.Gaussian.normSq w) ≤
            2 * ((29 / 16 : Q) + 29 / 16) :=
          RFAP.ConstructiveFraction.mul_le_mul_of_nonneg_left_direct
            (add_le_add zNorm wNorm) (by decide)
        _ = 29 / 4 := by
          rw [addSameDenominator 29 29 16
            (qNatPositive 16 (by omega)).ne']
          rw [show (2 : Q) * ((29 + 29) / 16) =
            ((29 + 29) / 16) * 2 by ring1, divMul]
          apply RFAP.ConstructiveFraction.div_eq_div_of_cross_mul
            (qNatPositive 16 (by omega)).ne'
            (qNatPositive 4 (by omega)).ne'
          ring1)
  have zSquareNorm :
      RFAP.ConstructiveGaussian.Gaussian.normSq (z ^ 2) ≤
        (7 / 2 : Q) := by
    rw [pow_two, RFAP.ConstructiveGaussian.Gaussian.normSq_mul]
    calc
      RFAP.ConstructiveGaussian.Gaussian.normSq z *
          RFAP.ConstructiveGaussian.Gaussian.normSq z ≤
          (29 / 16 : Q) * (29 / 16) :=
        RFAP.ConstructiveFraction.mul_le_mul_direct zNorm zNorm
          (RFAP.ConstructiveGaussian.Gaussian.normSq_nonneg _)
          (RFAP.ConstructiveFraction.div_nonneg_direct
            (qNatNonnegative 29) (qNatPositive 16 (by omega)).le)
      _ ≤ 7 / 2 := by
        rw [RFAP.ConstructiveFraction.div_mul_div_direct]
        apply divLeDivOfCrossMul
          (RFAP.ConstructiveFraction.mul_pos_direct
            (qNatPositive 16 (by omega)) (qNatPositive 16 (by omega)))
          (qNatPositive 2 (by omega))
        calc
          (29 : Q) * 29 * 2 = 1682 := by ring1
          _ ≤ 1792 := RFAP.ConstructiveFraction.natCast_le_direct
            (m := 1682) (n := 1792) (by omega)
          _ = 7 * (16 * 16) := by ring1
  have wSquareNorm :
      RFAP.ConstructiveGaussian.Gaussian.normSq (w ^ 2) ≤
        (7 / 2 : Q) := by
    rw [pow_two, RFAP.ConstructiveGaussian.Gaussian.normSq_mul]
    calc
      RFAP.ConstructiveGaussian.Gaussian.normSq w *
          RFAP.ConstructiveGaussian.Gaussian.normSq w ≤
          (29 / 16 : Q) * (29 / 16) :=
        RFAP.ConstructiveFraction.mul_le_mul_direct wNorm wNorm
          (RFAP.ConstructiveGaussian.Gaussian.normSq_nonneg _)
          (RFAP.ConstructiveFraction.div_nonneg_direct
            (qNatNonnegative 29) (qNatPositive 16 (by omega)).le)
      _ ≤ 7 / 2 := by
        rw [RFAP.ConstructiveFraction.div_mul_div_direct]
        apply divLeDivOfCrossMul
          (RFAP.ConstructiveFraction.mul_pos_direct
            (qNatPositive 16 (by omega)) (qNatPositive 16 (by omega)))
          (qNatPositive 2 (by omega))
        calc
          (29 : Q) * 29 * 2 = 1682 := by ring1
          _ ≤ 1792 := RFAP.ConstructiveFraction.natCast_le_direct
            (m := 1682) (n := 1792) (by omega)
          _ = 7 * (16 * 16) := by ring1
  have squareSumNorm :
      RFAP.ConstructiveGaussian.Gaussian.normSq (z ^ 2 + w ^ 2) ≤
        (14 : Q) :=
    (RFAP.ConstructiveGaussian.Gaussian.normSq_add_le_two
      (z ^ 2) (w ^ 2)).trans (by
        calc
          2 * (RFAP.ConstructiveGaussian.Gaussian.normSq (z ^ 2) +
              RFAP.ConstructiveGaussian.Gaussian.normSq (w ^ 2)) ≤
              2 * ((7 / 2 : Q) + 7 / 2) :=
            RFAP.ConstructiveFraction.mul_le_mul_of_nonneg_left_direct
              (add_le_add zSquareNorm wSquareNorm) (by decide)
          _ = 14 := by
            rw [addSameDenominator 7 7 2
              (qNatPositive 2 (by omega)).ne']
            rw [show (2 : Q) * ((7 + 7) / 2) =
              ((7 + 7) / 2) * 2 by ring1, divMul]
            have twoNe : (2 : Q) ≠ 0 :=
              (qNatPositive 2 (by omega)).ne'
            apply RFAP.ConstructiveFraction.mul_right_cancel_of_ne twoNe
            rw [RFAP.ConstructiveFraction.div_mul_cancel_of_ne
              ((7 + 7) * 2) (2 : Q) twoNe]
            ring1)
  have factorization :
      CCL.Riemann.FinitePeriodExamples.quarticPolynomial.eval z -
          CCL.Riemann.FinitePeriodExamples.quarticPolynomial.eval w =
        (z - w) * (z + w) * (z ^ 2 + w ^ 2) := by
    unfold CCL.Riemann.FinitePeriodExamples.quarticPolynomial
    rw [CCL.PowerMonodromy.polynomial_eval,
      CCL.PowerMonodromy.polynomial_eval]
    unfold CCL.Riemann.FinitePeriodExamples.degreeFour
    ring1
  rw [← quarticPolynomial_eval_firstConnectorGridInput
      (firstConnectorEdgeSource edge),
    ← quarticPolynomial_eval_firstConnectorGridInput
      (firstConnectorEdgeTarget edge)]
  change RFAP.ConstructiveGaussian.Gaussian.normSq
      (CCL.Riemann.FinitePeriodExamples.quarticPolynomial.eval z -
        CCL.Riemann.FinitePeriodExamples.quarticPolynomial.eval w) ≤ _
  rw [factorization,
    RFAP.ConstructiveGaussian.Gaussian.normSq_mul,
    RFAP.ConstructiveGaussian.Gaussian.normSq_mul,
    firstConnectorGridInput_adjacent_normSq edge]
  have oneOverNonnegative : (0 : Q) ≤ 1 / 1024 :=
    RFAP.ConstructiveFraction.div_nonneg_direct
      (qNatNonnegative 1) (qNatPositive 1024 (by omega)).le
  have prefixLe :
      (1 / 1024 : Q) *
          RFAP.ConstructiveGaussian.Gaussian.normSq (z + w) ≤
        (1 / 1024 : Q) * (29 / 4) :=
    RFAP.ConstructiveFraction.mul_le_mul_of_nonneg_left_direct
      sumNorm oneOverNonnegative
  calc
    (1 / 1024 : Q) *
          RFAP.ConstructiveGaussian.Gaussian.normSq (z + w) *
        RFAP.ConstructiveGaussian.Gaussian.normSq (z ^ 2 + w ^ 2) ≤
        (1 / 1024 : Q) * (29 / 4) * 14 :=
      RFAP.ConstructiveFraction.mul_le_mul_direct prefixLe squareSumNorm
        (RFAP.ConstructiveGaussian.Gaussian.normSq_nonneg _)
        (RFAP.ConstructiveFraction.mul_nonneg_direct oneOverNonnegative
          (RFAP.ConstructiveFraction.div_nonneg_direct
            (qNatNonnegative 29) (qNatPositive 4 (by omega)).le))
    _ = 406 / 4096 := by
      rw [RFAP.ConstructiveFraction.div_mul_div_direct, divMul]
      apply RFAP.ConstructiveFraction.div_eq_div_of_cross_mul
        (RFAP.ConstructiveFraction.mul_ne_zero_direct
          (qNatPositive 1024 (by omega)).ne'
          (qNatPositive 4 (by omega)).ne')
        (qNatPositive 4096 (by omega)).ne'
      ring1
    _ ≤ 7 / 64 := by
      apply divLeDivOfCrossMul
        (qNatPositive 4096 (by omega)) (qNatPositive 64 (by omega))
      calc
        (406 : Q) * 64 = 25984 := by ring1
        _ ≤ 28672 := RFAP.ConstructiveFraction.natCast_le_direct
          (m := 25984) (n := 28672) (by omega)
        _ = 7 * 4096 := by ring1

private def explicitFirstConnectorSegment :
    CCL.Riemann.BranchCuts.ClearSegment
      CCL.Riemann.FinitePeriodExamples.quarticCurve.polynomial
      (CCL.Riemann.BranchCuts.Ambient
        CCL.Riemann.FinitePeriodExamples.quarticCurve)
      (point (-5 / 4) (-1 / 2)) (point (-1) (-1 / 2)) :=
  (firstConnectorSegment.castStart firstConnectorSegment_start_eq).castFinish
    firstConnectorSegment_finish_eq

private theorem firstConnectorSegment_variation_eq_explicit
    (left right : Q) :
    CCL.Riemann.ClearSheetContinuation.variationBound firstConnectorSegment
        left right =
      CCL.Riemann.ClearSheetContinuation.variationBound
        explicitFirstConnectorSegment left right := by
  unfold explicitFirstConnectorSegment
  cases firstConnectorSegment_start_eq
  cases firstConnectorSegment_finish_eq
  rfl

private theorem explicitFirstConnectorDenseLowerThirtyNine : (39 : Q) ≤
    RFAP.PolynomialBounds.denseLipschitzBound
      (CCL.Riemann.ClearSheetContinuation.segmentPolynomial
        explicitFirstConnectorSegment)
      CCL.Riemann.ClearSheetContinuation.parameterAmbient := by
  unfold CCL.Riemann.ClearSheetContinuation.segmentPolynomial
  change (39 : Q) ≤
    RFAP.PolynomialBounds.denseLipschitzBound
      (RFAP.PathPolynomial.composeLine
        CCL.Riemann.FinitePeriodExamples.quarticPolynomial
        (point (-5 / 4) (-1 / 2))
        (point (-1) (-1 / 2) - point (-5 / 4) (-1 / 2)))
      CCL.Riemann.ClearSheetContinuation.parameterAmbient
  rw [show point (-1) (-1 / 2) - point (-5 / 4) (-1 / 2) =
    point (1 / 4) 0 by
      apply RFAP.ConstructiveGaussian.Gaussian.ext <;>
        with_unfolding_all decide]
  exact firstConnectorDenseVariationLowerThirtyNine

private theorem explicitFirstConnectorDenseUpperForty :
    RFAP.PolynomialBounds.denseLipschitzBound
      (CCL.Riemann.ClearSheetContinuation.segmentPolynomial
        explicitFirstConnectorSegment)
      CCL.Riemann.ClearSheetContinuation.parameterAmbient < (40 : Q) := by
  unfold CCL.Riemann.ClearSheetContinuation.segmentPolynomial
  change
    RFAP.PolynomialBounds.denseLipschitzBound
      (RFAP.PathPolynomial.composeLine
        CCL.Riemann.FinitePeriodExamples.quarticPolynomial
        (point (-5 / 4) (-1 / 2))
        (point (-1) (-1 / 2) - point (-5 / 4) (-1 / 2)))
      CCL.Riemann.ClearSheetContinuation.parameterAmbient < (40 : Q)
  rw [show point (-1) (-1 / 2) - point (-5 / 4) (-1 / 2) =
    point (1 / 4) 0 by
      apply RFAP.ConstructiveGaussian.Gaussian.ext <;>
        with_unfolding_all decide]
  exact firstConnectorDenseVariationUpperForty

private theorem adjacentVariationBounds
    (left right : Q)
    (squareEq : (left - right) ^ 2 = (1 / 64 : Q)) :
    (39 / 64 : Q) ≤
        CCL.Riemann.ClearSheetContinuation.variationBound
          firstConnectorSegment left right ∧
      CCL.Riemann.ClearSheetContinuation.variationBound
          firstConnectorSegment left right < (40 / 64 : Q) := by
  let lipschitz : Q :=
    RFAP.PolynomialBounds.denseLipschitzBound
      (CCL.Riemann.ClearSheetContinuation.segmentPolynomial
        explicitFirstConnectorSegment)
      CCL.Riemann.ClearSheetContinuation.parameterAmbient
  have lipschitzLower : (39 : Q) ≤ lipschitz :=
    explicitFirstConnectorDenseLowerThirtyNine
  have lipschitzUpper : lipschitz < (40 : Q) :=
    explicitFirstConnectorDenseUpperForty
  rw [firstConnectorSegment_variation_eq_explicit,
    CCL.Riemann.ClearSheetContinuation.variationBound_eq_denseLipschitz,
    squareEq]
  change 39 / 64 ≤ lipschitz * (1 / 64) ∧
    lipschitz * (1 / 64) < 40 / 64
  have factorPositive : (0 : Q) < 1 / 64 :=
    RFAP.ConstructiveFraction.div_pos_direct
      (qNatPositive 1 (by omega)) (qNatPositive 64 (by omega))
  constructor
  · calc
      (39 / 64 : Q) = 39 * (1 / 64) := by
        simp only [RFAP.ConstructiveFraction.div_eq_mul_inv_direct,
          RFAP.ConstructiveFraction.one_mul]
      _ ≤ lipschitz * (1 / 64) :=
        RFAP.ConstructiveFraction.mul_le_mul_of_nonneg_right_direct
          lipschitzLower factorPositive.le
  · calc
      lipschitz * (1 / 64) < 40 * (1 / 64) :=
        RFAP.ConstructiveFraction.mul_lt_mul_of_pos_right_direct
          lipschitzUpper factorPositive
      _ = 40 / 64 := by
        simp only [RFAP.ConstructiveFraction.div_eq_mul_inv_direct,
          RFAP.ConstructiveFraction.one_mul]

private theorem adjacentEighthParameters (value : Q) :
    (value / 8 - (value + 1) / 8) ^ 2 = (1 / 64 : Q) := by
  have difference : value / 8 - (value + 1) / 8 = (-1) / 8 := by
    simp only [RFAP.ConstructiveFraction.div_eq_mul_inv_direct]
    ring1
  rw [difference, pow_two, RFAP.ConstructiveFraction.div_mul_div_direct]
  rw [show (-1 : Q) * (-1) = 1 by ring1,
    show (8 : Q) * 8 = 64 by ring1]

private theorem firstConnectorGridEndpoint_adjacentSquare (edge : Fin 8) :
    ((firstConnectorGridEndpoint (firstConnectorEdgeSource edge)).parameter -
      (firstConnectorGridEndpoint (firstConnectorEdgeTarget edge)).parameter) ^
        2 = (1 / 64 : Q) := by
  rcases finEightCases edge with h | h | h | h | h | h | h | h
  all_goals subst edge
  all_goals simp only [firstConnectorEdgeSource, firstConnectorEdgeTarget,
    firstConnectorGridEndpoint]
  all_goals apply adjacentEighthParameters

/-- Every one of the eight local dyadic edges has the same sharp finite
variation bracket. -/
theorem firstConnectorGridVariationBounds (edge : Fin 8) :
    (39 / 64 : Q) ≤
        CCL.Riemann.ClearSheetContinuation.variationBound
          firstConnectorSegment
          (firstConnectorGridEndpoint
            (firstConnectorEdgeSource edge)).parameter
          (firstConnectorGridEndpoint
            (firstConnectorEdgeTarget edge)).parameter ∧
      CCL.Riemann.ClearSheetContinuation.variationBound
          firstConnectorSegment
          (firstConnectorGridEndpoint
            (firstConnectorEdgeSource edge)).parameter
          (firstConnectorGridEndpoint
            (firstConnectorEdgeTarget edge)).parameter < (40 / 64 : Q) :=
  adjacentVariationBounds _ _
    (firstConnectorGridEndpoint_adjacentSquare edge)

/-- The sharp variation lower bound and the factorized displacement upper
bound leave a uniform half-unit prepared margin on every local edge. -/
theorem firstConnectorGridVariationMargin (edge : Fin 8) : (1 / 2 : Q) ≤
    CCL.Riemann.ClearSheetContinuation.variationBound firstConnectorSegment
        (firstConnectorGridEndpoint
          (firstConnectorEdgeSource edge)).parameter
        (firstConnectorGridEndpoint
          (firstConnectorEdgeTarget edge)).parameter -
      RFAP.ConstructiveGaussian.Gaussian.normSq
        (firstConnectorGridParameter (firstConnectorEdgeSource edge) -
          firstConnectorGridParameter (firstConnectorEdgeTarget edge)) := by
  calc
    (1 / 2 : Q) = 32 / 64 := by
      apply divEqOfNatDenominators
        (leftDenominator := 2) (rightDenominator := 64) <;>
        first | omega | ring1
    _ = 39 / 64 - 7 / 64 := by
      rw [subSameDenominator 39 7 64
        (qNatPositive 64 (by omega)).ne']
      rw [show (39 : Q) - 7 = 32 by ring1]
    _ ≤ CCL.Riemann.ClearSheetContinuation.variationBound
          firstConnectorSegment
          (firstConnectorGridEndpoint
            (firstConnectorEdgeSource edge)).parameter
          (firstConnectorGridEndpoint
            (firstConnectorEdgeTarget edge)).parameter -
        RFAP.ConstructiveGaussian.Gaussian.normSq
          (firstConnectorGridParameter (firstConnectorEdgeSource edge) -
            firstConnectorGridParameter (firstConnectorEdgeTarget edge)) :=
      RFAP.ConstructiveFraction.sub_le_sub_direct
        (firstConnectorGridVariationBounds edge).1
        (firstConnectorGridDisplacement_le edge)

/-! ## The first prepared mesh edge -/

theorem firstConnectorGridParameterZeroEq :
    firstConnectorGridParameter 0 = squareRootParameter 0 := by
  rw [squareRootParameter_zero_eq]
  simp only [firstConnectorGridParameter, reducedRational_eq_div]
  apply RFAP.ConstructiveGaussian.Gaussian.ext <;>
    simp only [pointReal, pointImaginary, Int.cast_neg, Int.cast_ofNat,
      Nat.cast_ofNat]

theorem firstConnectorStartBoxEq :
    firstConnectorStartOwner.track.initial.box = squareRootOwnerBox 0 0 := by
  with_unfolding_all rfl

theorem firstConnectorDerivativeMarginLe :
    CCL.Riemann.ClearSheetContinuation.squareRootDerivativeMargin
      firstConnectorSegment ≤ (1 / 4 : Q) := by
  with_unfolding_all decide

private theorem oneOver128LeOne : (1 / (16 * 8) : Q) ≤ 1 := by
  have denominatorPositive : (0 : Q) < 16 * 8 :=
    RFAP.ConstructiveFraction.mul_pos_direct
      (qNatPositive 16 (by omega)) (qNatPositive 8 (by omega))
  apply RFAP.ConstructiveFraction.le_of_mul_le_mul_right_direct
    (c := (16 : Q) * 8) _ denominatorPositive
  rw [RFAP.ConstructiveFraction.div_mul_cancel_of_ne _ _
    denominatorPositive.ne']
  calc
    (1 : Q) = 0 + 1 := by ring1
    _ ≤ 127 + 1 :=
      RFAP.ConstructiveFraction.add_le_add_right_direct
        (qNatNonnegative 127) 1
    _ = 1 * ((16 : Q) * 8) := by ring1

/-- The inherited branch owner retains a small explicit clearance at the
start of the first connector cell. -/
theorem firstConnectorStartClearance : (1 / (16 * 8) : Q) ≤
    firstConnectorStartOwner.track.initial.clearance.bound := by
  rw [show firstConnectorStartOwner.track.initial.clearance.bound =
    (squareRootOwner 0 0).track.initial.clearance.bound by
      with_unfolding_all rfl]
  unfold squareRootOwner
  rw [CCL.Riemann.ExactQuadraticOwnerClearance.directOwnerOfBox_initial_clearance_bound]
  apply CCL.Riemann.ExactQuadraticOwnerClearance.le_directBoundaryClearance_bound
  all_goals rw [← firstConnectorGridParameterZeroEq]
  all_goals with_unfolding_all decide

/-- The inherited owner has the uniform geometric data requested by the
first depth-three mesh edge. -/
theorem firstConnectorStartReady :
    CCL.Riemann.PreparedSheetContinuation.AlreadyPrepared firstConnectorSegment
      CCL.Riemann.PreparedClearPathModels.zeroEndpoint firstConnectorStartOwner
        (firstConnectorEdgeRequest 0) := by
  refine ⟨?_, ?_, ?_⟩
  · rw [firstConnectorStartBoxEq]
    with_unfolding_all decide
  · exact
      (CCL.Riemann.UniformSquareRootPreparation.predictedClearance_le_oneOver128
        firstConnectorSegment
          (firstConnectorEdgeRequest 0).rootDiameter
          (firstConnectorEdgeRequest 0).rootDiameterPositive
          firstConnectorDerivativeMarginLe).trans firstConnectorStartClearance
  · change
      -CCL.Riemann.UniformSquareRootPreparation.rootAmbientRadius
          firstConnectorSegment ≤
          firstConnectorStartOwner.track.initial.box.xLower ∧
        firstConnectorStartOwner.track.initial.box.xUpper ≤
          CCL.Riemann.UniformSquareRootPreparation.rootAmbientRadius
            firstConnectorSegment ∧
        -CCL.Riemann.UniformSquareRootPreparation.rootAmbientRadius
          firstConnectorSegment ≤
          firstConnectorStartOwner.track.initial.box.yLower ∧
        firstConnectorStartOwner.track.initial.box.yUpper ≤
          CCL.Riemann.UniformSquareRootPreparation.rootAmbientRadius
            firstConnectorSegment
    have threeLe :=
      CCL.Riemann.UniformSquareRootPreparation.three_le_rootAmbientRadius
        firstConnectorSegment
    exact ⟨(RFAP.ConstructiveFraction.neg_le_neg_direct threeLe).trans
        (by with_unfolding_all decide),
      (by with_unfolding_all decide :
        firstConnectorStartOwner.track.initial.box.xUpper ≤ (3 : Q)).trans
          threeLe,
      (RFAP.ConstructiveFraction.neg_le_neg_direct threeLe).trans
        (by with_unfolding_all decide),
      (by with_unfolding_all decide :
        firstConnectorStartOwner.track.initial.box.yUpper ≤ (3 : Q)).trans
          threeLe⟩

/-- Cached successful moving reset for the first mesh edge. -/
def firstConnectorMovingCache :
    { reset : CCL.Riemann.ExactQuadraticOwnerClearance.MovingRecenter
        _ firstConnectorStartOwner //
      CCL.Riemann.ExactQuadraticOwnerClearance.movingRecenter?
        firstConnectorStartOwner = some reset } := by
  generalize found :
    CCL.Riemann.ExactQuadraticOwnerClearance.movingRecenter?
      firstConnectorStartOwner = result
  cases result with
  | none =>
      have succeeds :
          (CCL.Riemann.ExactQuadraticOwnerClearance.movingRecenter?
            firstConnectorStartOwner).isSome = true := by
        with_unfolding_all rfl
      rw [found] at succeeds
      contradiction
  | some reset => exact ⟨reset, rfl⟩

def firstConnectorMoving := firstConnectorMovingCache.1

theorem firstConnectorMovingFound :
    CCL.Riemann.ExactQuadraticOwnerClearance.movingRecenter?
      firstConnectorStartOwner = some firstConnectorMoving :=
  firstConnectorMovingCache.2

theorem firstConnectorRecenteredEq :
    CCL.Riemann.PreparedSheetContinuation.recentered
        firstConnectorStartOwner = firstConnectorMoving.owner :=
  CCL.Riemann.PreparedSheetContinuation.recentered_eq_of_movingRecenter_eq_some
    firstConnectorStartOwner firstConnectorMoving firstConnectorMovingFound

theorem firstConnectorMovingBoxEq :
    firstConnectorMoving.ownerBox = firstConnectorBoxOne := by
  rw [RFAP.Boxes.Box.mk.injEq]
  with_unfolding_all decide

/-- The first moving reset has a full unit of direct boundary clearance. -/
theorem firstConnectorMovingClearance : (1 : Q) ≤
    firstConnectorMoving.owner.track.initial.clearance.bound := by
  rw [firstConnectorMoving.ownerDirectClearanceBound]
  apply CCL.Riemann.ExactQuadraticOwnerClearance.le_directBoundaryClearance_bound
  all_goals rw [firstConnectorMovingBoxEq]
  all_goals change (1 : Q) ≤ _
  all_goals rw [show
    CCL.Riemann.FinitePeriodExamples.quarticCurve.polynomial.eval
        (firstConnectorSegment.pointAt
          CCL.Riemann.PreparedClearPathModels.zeroEndpoint.parameter) =
      squareRootParameter 0 by with_unfolding_all rfl]
  all_goals with_unfolding_all decide

theorem firstConnectorEdgeZeroVariationLtOne :
    CCL.Riemann.ClearSheetContinuation.variationBound firstConnectorSegment
        CCL.Riemann.PreparedClearPathModels.zeroEndpoint.parameter
          (firstConnectorEdgeRequest 0).endpoint.parameter < (1 : Q) := by
  change CCL.Riemann.ClearSheetContinuation.variationBound firstConnectorSegment
      (firstConnectorMeshEndpoint 0).parameter
        (firstConnectorMeshEndpoint 1).parameter < (1 : Q)
  rw [firstConnectorMeshEndpoint_parameter 0,
    firstConnectorMeshEndpoint_parameter 1]
  exact (firstConnectorGridVariationBounds 0).2.trans (by
    apply (RFAP.ConstructiveFraction.div_lt_iff_pos
      (qNatPositive 64 (by omega))).2
    rw [one_mul]
    exact RFAP.ConstructiveFraction.natCast_lt_direct (by decide : 40 < 64))

theorem firstConnectorRecenteredReady :
    CCL.Riemann.PreparedSheetContinuation.AlreadyPrepared firstConnectorSegment
      CCL.Riemann.PreparedClearPathModels.zeroEndpoint
        (CCL.Riemann.PreparedSheetContinuation.recentered
          firstConnectorStartOwner) (firstConnectorEdgeRequest 0) := by
  rw [firstConnectorRecenteredEq]
  refine ⟨?_, ?_, ?_⟩
  · rw [firstConnectorMoving.ownerInitialBox, firstConnectorMovingBoxEq]
    with_unfolding_all decide
  · exact
      (CCL.Riemann.UniformSquareRootPreparation.predictedClearance_le_oneOver128
        firstConnectorSegment
          (firstConnectorEdgeRequest 0).rootDiameter
          (firstConnectorEdgeRequest 0).rootDiameterPositive
          firstConnectorDerivativeMarginLe).trans
        (oneOver128LeOne.trans firstConnectorMovingClearance)
  · rw [firstConnectorMoving.ownerInitialBox, firstConnectorMovingBoxEq]
    change
      -CCL.Riemann.UniformSquareRootPreparation.rootAmbientRadius
          firstConnectorSegment ≤ firstConnectorBoxOne.xLower ∧
        firstConnectorBoxOne.xUpper ≤
          CCL.Riemann.UniformSquareRootPreparation.rootAmbientRadius
            firstConnectorSegment ∧
        -CCL.Riemann.UniformSquareRootPreparation.rootAmbientRadius
          firstConnectorSegment ≤ firstConnectorBoxOne.yLower ∧
        firstConnectorBoxOne.yUpper ≤
          CCL.Riemann.UniformSquareRootPreparation.rootAmbientRadius
            firstConnectorSegment
    have threeLe :=
      CCL.Riemann.UniformSquareRootPreparation.three_le_rootAmbientRadius
        firstConnectorSegment
    exact ⟨(RFAP.ConstructiveFraction.neg_le_neg_direct threeLe).trans
        (by with_unfolding_all decide),
      (by with_unfolding_all decide :
        firstConnectorBoxOne.xUpper ≤ (3 : Q)).trans threeLe,
      (RFAP.ConstructiveFraction.neg_le_neg_direct threeLe).trans
        (by with_unfolding_all decide),
      (by with_unfolding_all decide :
        firstConnectorBoxOne.yUpper ≤ (3 : Q)).trans threeLe⟩

theorem firstConnectorRecenteredCarries :
    CCL.Riemann.ClearSheetContinuation.variationBound firstConnectorSegment
        CCL.Riemann.PreparedClearPathModels.zeroEndpoint.parameter
          (firstConnectorEdgeRequest 0).endpoint.parameter <
      (CCL.Riemann.PreparedSheetContinuation.recentered
        firstConnectorStartOwner).track.initial.clearance.bound := by
  rw [firstConnectorRecenteredEq]
  exact firstConnectorEdgeZeroVariationLtOne.trans_le
    firstConnectorMovingClearance

/-- The canonical bounded preparation accepts the first displayed edge. -/
theorem firstConnectorCanonicalSmall :
    CCL.Riemann.ClearSheetContinuation.variationBound firstConnectorSegment
        CCL.Riemann.PreparedClearPathModels.zeroEndpoint.parameter
          (firstConnectorEdgeRequest 0).endpoint.parameter <
      (CCL.Riemann.PreparedSheetContinuation.prepared firstConnectorSegment
        CCL.Riemann.PreparedClearPathModels.zeroEndpoint firstConnectorStartOwner
          (firstConnectorEdgeRequest 0)).track.initial.clearance.bound :=
  CCL.Riemann.PreparedSheetContinuation.variation_lt_prepared_of_ready_of_recenteredCarries
    firstConnectorSegment
      CCL.Riemann.PreparedClearPathModels.zeroEndpoint firstConnectorStartOwner
        (firstConnectorEdgeRequest 0) firstConnectorStartReady
          firstConnectorRecenteredReady firstConnectorRecenteredCarries

/-! ## Stable transport data for the first edge -/

theorem firstConnectorGridParameterNormSqLe (index : Fin 9) :
    RFAP.ConstructiveGaussian.Gaussian.normSq
      (firstConnectorGridParameter index) ≤ (256 : Q) := by
  rw [← quarticPolynomial_eval_firstConnectorGridInput]
  unfold CCL.Riemann.FinitePeriodExamples.quarticPolynomial
  rw [CCL.PowerMonodromy.polynomial_eval]
  unfold CCL.Riemann.FinitePeriodExamples.degreeFour
  have inputLeTwo : RFAP.ConstructiveGaussian.Gaussian.normSq
      (firstConnectorGridInput index) ≤ (2 : Q) :=
    (firstConnectorGridInput_normSq_le index).trans (by
      have sixteenPositive : (0 : Q) < 16 := by decide
      apply RFAP.ConstructiveFraction.le_of_mul_le_mul_right_direct
        (c := (16 : Q)) _ sixteenPositive
      rw [RFAP.ConstructiveFraction.div_mul_cancel_of_ne _ _
        sixteenPositive.ne']
      calc
        (29 : Q) ≤ 32 :=
          RFAP.ConstructiveFraction.natCast_le_direct
            (by decide : 29 ≤ 32)
        _ = 2 * 16 := by ring1)
  have fourthLe :
      RFAP.ConstructiveGaussian.Gaussian.normSq
          (firstConnectorGridInput index) ^ 4 ≤ (2 : Q) ^ 4 :=
    RFAP.ConstructiveFraction.pow_le_pow_direct
      (RFAP.ConstructiveGaussian.Gaussian.normSq_nonneg _)
        inputLeTwo 4
  calc
    RFAP.ConstructiveGaussian.Gaussian.normSq
        (firstConnectorGridInput index ^ 4 - 1) ≤
      2 * (RFAP.ConstructiveGaussian.Gaussian.normSq
          (firstConnectorGridInput index ^ 4) +
        RFAP.ConstructiveGaussian.Gaussian.normSq 1) :=
      RFAP.ConstructiveGaussian.Gaussian.normSq_sub_le_two _ _
    _ = 2 * (RFAP.ConstructiveGaussian.Gaussian.normSq
          (firstConnectorGridInput index) ^ 4 + 1) := by
      rw [RFAP.ConstructiveGaussian.Gaussian.normSq_pow,
        RFAP.ConstructiveGaussian.Gaussian.normSq_one]
    _ ≤ 2 * ((2 : Q) ^ 4 + 1) :=
      RFAP.ConstructiveFraction.mul_le_mul_of_nonneg_left_direct
        (add_le_add fourthLe le_rfl) (qNatNonnegative 2)
    _ = (34 : Q) := by ring1
    _ ≤ (256 : Q) :=
      RFAP.ConstructiveFraction.natCast_le_direct (by decide : 34 ≤ 256)

theorem firstConnectorAdjacentParametersDifferent (edge : Fin 8) :
    firstConnectorGridParameter (firstConnectorEdgeSource edge) ≠
      firstConnectorGridParameter (firstConnectorEdgeTarget edge) := by
  rcases finEightCases edge with h | h | h | h | h | h | h | h
  all_goals subst edge
  all_goals with_unfolding_all decide +revert

theorem firstConnectorStartAmbientEq :
    firstConnectorStartOwner.ambient = squareRootOwnerBox 0 0 := by
  with_unfolding_all rfl

theorem firstConnectorStartDominance :
    CCL.Riemann.ExactQuadraticOwnerClearance.AmbientClearanceDominance
      firstConnectorStartOwner := by
  change CCL.Riemann.ExactQuadraticOwnerClearance.AmbientClearanceDominance
    (squareRootOwner 0 0)
  unfold squareRootOwner
  exact CCL.Riemann.ExactQuadraticOwnerClearance.directOwnerOfBox_ambientClearanceDominance
    _ _ _ _ _ _ _ _ _

theorem firstConnectorStartBudget :
    CCL.Riemann.ExactQuadraticOwnerClearance.QuadraticAmbientBudget
      firstConnectorStartOwner := by
  apply CCL.Riemann.ExactQuadraticOwnerClearance.quadraticAmbientBudget_of_box
    firstConnectorStartOwner (squareRootOwnerBox 0 0)
      firstConnectorStartBoxEq firstConnectorStartAmbientEq
  · rw [show
      CCL.Riemann.FinitePeriodExamples.quarticCurve.polynomial.eval
          (firstConnectorSegment.pointAt
            CCL.Riemann.PreparedClearPathModels.zeroEndpoint.parameter) =
        firstConnectorGridParameter 0 by
          exact quarticPolynomial_eval_firstConnectorMeshEndpoint 0]
    exact firstConnectorGridParameterNormSqLe 0
  all_goals with_unfolding_all decide

theorem firstConnectorRecenteredBudget :
    CCL.Riemann.ExactQuadraticOwnerClearance.QuadraticAmbientBudget
      (CCL.Riemann.PreparedSheetContinuation.recentered
        firstConnectorStartOwner) := by
  rw [firstConnectorRecenteredEq]
  apply CCL.Riemann.ExactQuadraticOwnerClearance.quadraticAmbientBudget_of_box
    firstConnectorMoving.owner firstConnectorBoxOne
  · exact firstConnectorMoving.ownerInitialBox.trans
      firstConnectorMovingBoxEq
  · exact firstConnectorMoving.ownerAmbientBox.trans firstConnectorMovingBoxEq
  · rw [show
      CCL.Riemann.FinitePeriodExamples.quarticCurve.polynomial.eval
          (firstConnectorSegment.pointAt
            CCL.Riemann.PreparedClearPathModels.zeroEndpoint.parameter) =
        firstConnectorGridParameter 0 by
          exact quarticPolynomial_eval_firstConnectorMeshEndpoint 0]
    exact firstConnectorGridParameterNormSqLe 0
  all_goals with_unfolding_all decide

def firstConnectorCachedSource :=
  CCL.Riemann.PreparedSheetContinuation.CachedSource.canonical
    firstConnectorSegment CCL.Riemann.PreparedClearPathModels.zeroEndpoint
      firstConnectorStartOwner (firstConnectorEdgeRequest 0)

theorem firstConnectorPreparedDominance :
    CCL.Riemann.ExactQuadraticOwnerClearance.AmbientClearanceDominance
      firstConnectorCachedSource.preparedOwner :=
  CCL.Riemann.PreparedSheetContinuation.prepared_ambientClearanceDominance_of_ready_of_recenteredCarries
      firstConnectorSegment CCL.Riemann.PreparedClearPathModels.zeroEndpoint
        firstConnectorStartOwner (firstConnectorEdgeRequest 0)
          firstConnectorStartReady firstConnectorRecenteredReady
            firstConnectorRecenteredCarries firstConnectorStartDominance

theorem firstConnectorPreparedBudget :
    CCL.Riemann.ExactQuadraticOwnerClearance.QuadraticAmbientBudget
      firstConnectorCachedSource.preparedOwner :=
  CCL.Riemann.PreparedSheetContinuation.prepared_quadraticAmbientBudget_of_ready_of_recenteredCarries
      firstConnectorSegment CCL.Riemann.PreparedClearPathModels.zeroEndpoint
        firstConnectorStartOwner (firstConnectorEdgeRequest 0)
          firstConnectorStartReady firstConnectorRecenteredReady
            firstConnectorRecenteredCarries firstConnectorStartBudget
              firstConnectorRecenteredBudget

theorem firstConnectorEdgeZeroVariationMargin : (1 / 2 : Q) ≤
    CCL.Riemann.ClearSheetContinuation.variationBound firstConnectorSegment
        CCL.Riemann.PreparedClearPathModels.zeroEndpoint.parameter
          (firstConnectorEdgeRequest 0).endpoint.parameter -
      RFAP.ConstructiveGaussian.Gaussian.normSq
        (CCL.Riemann.FinitePeriodExamples.quarticCurve.polynomial.eval
            (firstConnectorSegment.pointAt
              CCL.Riemann.PreparedClearPathModels.zeroEndpoint.parameter) -
          CCL.Riemann.FinitePeriodExamples.quarticCurve.polynomial.eval
            (firstConnectorSegment.pointAt
              (firstConnectorEdgeRequest 0).endpoint.parameter)) := by
  change (1 / 2 : Q) ≤
    CCL.Riemann.ClearSheetContinuation.variationBound firstConnectorSegment
        (firstConnectorMeshEndpoint 0).parameter
          (firstConnectorMeshEndpoint 1).parameter -
      RFAP.ConstructiveGaussian.Gaussian.normSq
        (CCL.Riemann.FinitePeriodExamples.quarticCurve.polynomial.eval
            (firstConnectorSegment.pointAt
              (firstConnectorMeshEndpoint 0).parameter) -
          CCL.Riemann.FinitePeriodExamples.quarticCurve.polynomial.eval
            (firstConnectorSegment.pointAt
              (firstConnectorMeshEndpoint 1).parameter))
  rw [firstConnectorMeshEndpoint_parameter 0,
    firstConnectorMeshEndpoint_parameter 1]
  change (1 / 2 : Q) ≤
    CCL.Riemann.ClearSheetContinuation.variationBound firstConnectorSegment
        (firstConnectorGridEndpoint 0).parameter
          (firstConnectorGridEndpoint 1).parameter -
      RFAP.ConstructiveGaussian.Gaussian.normSq
        (CCL.Riemann.FinitePeriodExamples.quarticPolynomial.eval
            (firstConnectorSegment.pointAt
              (firstConnectorGridEndpoint 0).parameter) -
          CCL.Riemann.FinitePeriodExamples.quarticPolynomial.eval
            (firstConnectorSegment.pointAt
              (firstConnectorGridEndpoint 1).parameter))
  rw [
    quarticPolynomial_eval_firstConnectorGridEndpoint 0,
    quarticPolynomial_eval_firstConnectorGridEndpoint 1]
  exact firstConnectorGridVariationMargin 0

theorem firstConnectorRecenteredMargin : (1 / 2 : Q) ≤
    (CCL.Riemann.PreparedSheetContinuation.recentered
        firstConnectorStartOwner).track.initial.clearance.bound -
      RFAP.ConstructiveGaussian.Gaussian.normSq
        (CCL.Riemann.FinitePeriodExamples.quarticCurve.polynomial.eval
            (firstConnectorSegment.pointAt
              CCL.Riemann.PreparedClearPathModels.zeroEndpoint.parameter) -
          CCL.Riemann.FinitePeriodExamples.quarticCurve.polynomial.eval
            (firstConnectorSegment.pointAt
              (firstConnectorEdgeRequest 0).endpoint.parameter)) :=
  firstConnectorEdgeZeroVariationMargin.trans
    (RFAP.ConstructiveFraction.sub_le_sub_right_direct
      firstConnectorRecenteredCarries.le _)

theorem firstConnectorPreparedMargin : (1 / 2 : Q) ≤
    firstConnectorCachedSource.preparedOwner.track.initial.clearance.bound -
      RFAP.ConstructiveGaussian.Gaussian.normSq
        (CCL.Riemann.FinitePeriodExamples.quarticCurve.polynomial.eval
            (firstConnectorSegment.pointAt
              CCL.Riemann.PreparedClearPathModels.zeroEndpoint.parameter) -
          CCL.Riemann.FinitePeriodExamples.quarticCurve.polynomial.eval
            (firstConnectorSegment.pointAt
              (firstConnectorEdgeRequest 0).endpoint.parameter)) :=
  CCL.Riemann.PreparedSheetContinuation.prepared_margin_lower_of_ready_of_recenteredCarries
      firstConnectorSegment CCL.Riemann.PreparedClearPathModels.zeroEndpoint
        firstConnectorStartOwner (firstConnectorEdgeRequest 0)
          firstConnectorStartReady firstConnectorRecenteredReady
            firstConnectorRecenteredCarries (1 / 2) _
              firstConnectorEdgeZeroVariationMargin
                firstConnectorRecenteredMargin

theorem firstConnectorEdgeZeroAdvanceCache :
    CCL.Riemann.PreparedSheetContinuation.QuadraticAdvanceCache
      firstConnectorSegment firstConnectorSegment_withinAmbient
        CCL.Riemann.PreparedClearPathModels.zeroEndpoint
          firstConnectorStartOwner (firstConnectorEdgeRequest 0)
            firstConnectorCachedSource firstConnectorCanonicalSmall := by
  apply CCL.Riemann.PreparedSheetContinuation.quadraticAdvanceCache
  · rw [show
      CCL.Riemann.FinitePeriodExamples.quarticCurve.polynomial.eval
          (firstConnectorSegment.pointAt
            CCL.Riemann.PreparedClearPathModels.zeroEndpoint.parameter) =
        firstConnectorGridParameter 0 by
          exact quarticPolynomial_eval_firstConnectorMeshEndpoint 0,
      show
      CCL.Riemann.FinitePeriodExamples.quarticCurve.polynomial.eval
          (firstConnectorSegment.pointAt
            (firstConnectorEdgeRequest 0).endpoint.parameter) =
        firstConnectorGridParameter 1 by
          exact quarticPolynomial_eval_firstConnectorMeshEndpoint 1]
    exact firstConnectorAdjacentParametersDifferent 0
  · exact firstConnectorDerivativeMarginLe
  · exact firstConnectorPreparedDominance
  · exact firstConnectorPreparedMargin
  · exact firstConnectorPreparedBudget
  · rw [show
      CCL.Riemann.FinitePeriodExamples.quarticCurve.polynomial.eval
          (firstConnectorSegment.pointAt
            (firstConnectorEdgeRequest 0).endpoint.parameter) =
        firstConnectorGridParameter 1 by
          exact quarticPolynomial_eval_firstConnectorMeshEndpoint 1]
    exact firstConnectorGridParameterNormSqLe 1

/-! ## Exact first reset and the transported endpoint-one owner -/

theorem firstConnectorStartParameterEq :
    CCL.Riemann.FinitePeriodExamples.quarticCurve.polynomial.eval
        (firstConnectorSegment.pointAt
          CCL.Riemann.PreparedClearPathModels.zeroEndpoint.parameter) =
      squareRootParameter 0 := by
  with_unfolding_all rfl

theorem firstConnectorEdgeZeroVariationLower : (39 / 64 : Q) ≤
    CCL.Riemann.ClearSheetContinuation.variationBound firstConnectorSegment
      CCL.Riemann.PreparedClearPathModels.zeroEndpoint.parameter
        (firstConnectorEdgeRequest 0).endpoint.parameter := by
  change (39 / 64 : Q) ≤
    CCL.Riemann.ClearSheetContinuation.variationBound firstConnectorSegment
      (firstConnectorMeshEndpoint 0).parameter
        (firstConnectorMeshEndpoint 1).parameter
  rw [firstConnectorMeshEndpoint_parameter 0,
    firstConnectorMeshEndpoint_parameter 1]
  exact (firstConnectorGridVariationBounds 0).1

private theorem firstConnectorStartClearanceLeBottom :
    firstConnectorStartOwner.track.initial.clearance.bound ≤
      CCL.Riemann.ExactQuadraticOwnerClearance.directHorizontalClearanceBound
        (squareRootParameter 0) (squareRootOwnerBox 0 0)
          (squareRootOwnerBox 0 0).yLower := by
  rw [show firstConnectorStartOwner.track.initial.clearance.bound =
    (squareRootOwner 0 0).track.initial.clearance.bound by
      with_unfolding_all rfl]
  unfold squareRootOwner
  rw [CCL.Riemann.ExactQuadraticOwnerClearance.directOwnerOfBox_initial_clearance_bound,
    CCL.Riemann.ExactQuadraticOwnerClearance.directBoundaryClearance_bound]
  exact (min_le_right _ _).trans
    ((min_le_right _ _).trans (min_le_left _ _))

private theorem firstConnectorStartBottomLeVariation :
    CCL.Riemann.ExactQuadraticOwnerClearance.directHorizontalClearanceBound
        (squareRootParameter 0) (squareRootOwnerBox 0 0)
          (squareRootOwnerBox 0 0).yLower ≤
      CCL.Riemann.ClearSheetContinuation.variationBound firstConnectorSegment
        CCL.Riemann.PreparedClearPathModels.zeroEndpoint.parameter
          (firstConnectorEdgeRequest 0).endpoint.parameter := by
  have bottomEq :
      CCL.Riemann.ExactQuadraticOwnerClearance.directHorizontalClearanceBound
          (squareRootParameter 0) (squareRootOwnerBox 0 0)
            (squareRootOwnerBox 0 0).yLower =
        ((4 * 8) / (9 * 9) : Q) := by
    with_unfolding_all decide
  rw [bottomEq]
  apply (show ((4 * 8) / (9 * 9) : Q) ≤ 39 / 64 by
    have ninePositive : (0 : Q) < 9 := by
      simpa only [Nat.cast_ofNat] using qNatPositive 9 (by omega)
    have sixtyFourPositive : (0 : Q) < 64 := by
      simpa only [Nat.cast_ofNat] using qNatPositive 64 (by omega)
    apply divLeDivOfCrossMul
      (RFAP.ConstructiveFraction.mul_pos_direct
        ninePositive ninePositive) sixtyFourPositive
    calc
      ((4 * 8 : Q) * 64) = 2048 := by ring1
      _ ≤ 3159 := by
        simpa only [Nat.cast_ofNat] using
          (RFAP.ConstructiveFraction.natCast_le_direct
            (by decide : 2048 ≤ 3159))
      _ = 39 * (9 * 9) := by ring1).trans
  exact firstConnectorEdgeZeroVariationLower

theorem firstConnectorStartNotCarries :
    ¬ CCL.Riemann.ClearSheetContinuation.variationBound firstConnectorSegment
        CCL.Riemann.PreparedClearPathModels.zeroEndpoint.parameter
          (firstConnectorEdgeRequest 0).endpoint.parameter <
      firstConnectorStartOwner.track.initial.clearance.bound := by
  apply not_lt_of_ge
  exact firstConnectorStartClearanceLeBottom.trans
    firstConnectorStartBottomLeVariation

theorem firstConnectorStrengthenedNotCarries :
    ¬ CCL.Riemann.ClearSheetContinuation.variationBound firstConnectorSegment
        CCL.Riemann.PreparedClearPathModels.zeroEndpoint.parameter
          (firstConnectorEdgeRequest 0).endpoint.parameter <
      (CCL.Riemann.ExactQuadraticOwnerClearance.strengthenQuadraticOwner
        firstConnectorStartOwner).track.initial.clearance.bound := by
  let leftNonzero :
      CCL.Riemann.SquareRootContinuationChain.Owner.verticalDeterminant
        (CCL.Riemann.FinitePeriodExamples.quarticCurve.polynomial.eval
          (firstConnectorSegment.pointAt
            CCL.Riemann.PreparedClearPathModels.zeroEndpoint.parameter))
          firstConnectorStartOwner.track.initial.box.xLower ≠ 0 := by
    simpa only [firstConnectorStartParameterEq, firstConnectorStartBoxEq]
      using squareRootOwner_leftNonzero 0 0
  let rightNonzero :
      CCL.Riemann.SquareRootContinuationChain.Owner.verticalDeterminant
        (CCL.Riemann.FinitePeriodExamples.quarticCurve.polynomial.eval
          (firstConnectorSegment.pointAt
            CCL.Riemann.PreparedClearPathModels.zeroEndpoint.parameter))
          firstConnectorStartOwner.track.initial.box.xUpper ≠ 0 := by
    simpa only [firstConnectorStartParameterEq, firstConnectorStartBoxEq]
      using squareRootOwner_rightNonzero 0 0
  let bottomNonzero :
      CCL.Riemann.SquareRootContinuationChain.Owner.horizontalDeterminant
        (CCL.Riemann.FinitePeriodExamples.quarticCurve.polynomial.eval
          (firstConnectorSegment.pointAt
            CCL.Riemann.PreparedClearPathModels.zeroEndpoint.parameter))
          firstConnectorStartOwner.track.initial.box.yLower ≠ 0 := by
    simpa only [firstConnectorStartParameterEq, firstConnectorStartBoxEq]
      using squareRootOwner_bottomNonzero 0 0
  let topNonzero :
      CCL.Riemann.SquareRootContinuationChain.Owner.horizontalDeterminant
        (CCL.Riemann.FinitePeriodExamples.quarticCurve.polynomial.eval
          (firstConnectorSegment.pointAt
            CCL.Riemann.PreparedClearPathModels.zeroEndpoint.parameter))
          firstConnectorStartOwner.track.initial.box.yUpper ≠ 0 := by
    simpa only [firstConnectorStartParameterEq, firstConnectorStartBoxEq]
      using squareRootOwner_topNonzero 0 0
  apply not_lt_of_ge
  rw [CCL.Riemann.ExactQuadraticOwnerClearance.strengthenQuadraticOwner_clearance_eq_max
    firstConnectorStartOwner
      leftNonzero rightNonzero bottomNonzero topNonzero]
  apply max_le
  · exact firstConnectorStartClearanceLeBottom.trans
      firstConnectorStartBottomLeVariation
  · rw [CCL.Riemann.ExactQuadraticOwnerClearance.directBoundaryClearance_bound]
    calc
      min _ (min _ (min _ _)) ≤
          CCL.Riemann.ExactQuadraticOwnerClearance.directHorizontalClearanceBound
              (CCL.Riemann.FinitePeriodExamples.quarticCurve.polynomial.eval
                (firstConnectorSegment.pointAt
                  CCL.Riemann.PreparedClearPathModels.zeroEndpoint.parameter))
              firstConnectorStartOwner.track.initial.box
                firstConnectorStartOwner.track.initial.box.yLower :=
        (min_le_right _ _).trans
          ((min_le_right _ _).trans (min_le_left _ _))
      _ = CCL.Riemann.ExactQuadraticOwnerClearance.directHorizontalClearanceBound
          (squareRootParameter 0)
            (squareRootOwnerBox 0 0) (squareRootOwnerBox 0 0).yLower := by
        simp only [firstConnectorStartParameterEq, firstConnectorStartBoxEq]
      _ ≤ CCL.Riemann.ClearSheetContinuation.variationBound
          firstConnectorSegment
            CCL.Riemann.PreparedClearPathModels.zeroEndpoint.parameter
              (firstConnectorEdgeRequest 0).endpoint.parameter :=
        firstConnectorStartBottomLeVariation

theorem firstConnectorPreparedEqRecentered :
    CCL.Riemann.PreparedSheetContinuation.prepared firstConnectorSegment
        CCL.Riemann.PreparedClearPathModels.zeroEndpoint
          firstConnectorStartOwner (firstConnectorEdgeRequest 0) =
      CCL.Riemann.PreparedSheetContinuation.recentered
        firstConnectorStartOwner :=
  CCL.Riemann.PreparedSheetContinuation.prepared_eq_recentered_of_ready
    firstConnectorSegment CCL.Riemann.PreparedClearPathModels.zeroEndpoint
      firstConnectorStartOwner (firstConnectorEdgeRequest 0)
        firstConnectorStartReady firstConnectorStartNotCarries
          firstConnectorStrengthenedNotCarries firstConnectorRecenteredReady
            firstConnectorRecenteredCarries

private theorem quarterSquare_le_nineSixteenths (bound : Q)
    (nonnegative : 0 ≤ bound) (upper : bound ≤ 3 / 2) :
    bound ^ 2 / 4 ≤ (9 / 16 : Q) := by
  have squareLe : bound ^ 2 ≤ (3 / 2 : Q) ^ 2 :=
    RFAP.ConstructiveFraction.pow_le_pow_direct nonnegative upper 2
  calc
    bound ^ 2 / 4 ≤ (3 / 2 : Q) ^ 2 / 4 := by
      change bound ^ 2 * (4 : Q)⁻¹ ≤ (3 / 2 : Q) ^ 2 * (4 : Q)⁻¹
      exact RFAP.ConstructiveFraction.mul_le_mul_of_nonneg_right_direct
        squareLe (RFAP.ConstructiveFraction.inv_pos_direct (by decide)).le
    _ = (9 / 16 : Q) := by with_unfolding_all decide

private theorem quarterSquare_le_threeHalves_of_le_thirteenEighths
    (bound : Q) (nonnegative : 0 ≤ bound) (upper : bound ≤ 13 / 8) :
    bound ^ 2 / 4 ≤ (3 / 2 : Q) := by
  have squareLe : bound ^ 2 ≤ (13 / 8 : Q) ^ 2 :=
    RFAP.ConstructiveFraction.pow_le_pow_direct nonnegative upper 2
  calc
    bound ^ 2 / 4 ≤ (13 / 8 : Q) ^ 2 / 4 := by
      change bound ^ 2 * (4 : Q)⁻¹ ≤ (13 / 8 : Q) ^ 2 * (4 : Q)⁻¹
      exact RFAP.ConstructiveFraction.mul_le_mul_of_nonneg_right_direct
        squareLe (RFAP.ConstructiveFraction.inv_pos_direct (by decide)).le
    _ ≤ (3 / 2 : Q) := by with_unfolding_all decide

theorem firstConnectorRecenteredAmbientLeftLeThirteenEighths :
    (CCL.Riemann.PreparedSheetContinuation.recentered
      firstConnectorStartOwner).track.initial.ambientLeftClearance.bound ≤
        (13 / 8 : Q) := by
  rw [firstConnectorRecenteredEq,
    firstConnectorMoving.ownerAmbientLeftClearanceBound,
    CCL.Riemann.ExactQuadraticOwnerClearance.directBoundaryClearance_bound,
    firstConnectorMovingBoxEq,
    show
      CCL.Riemann.FinitePeriodExamples.quarticCurve.polynomial.eval
          (firstConnectorSegment.pointAt
            CCL.Riemann.PreparedClearPathModels.zeroEndpoint.parameter) =
        firstConnectorGridParameter 0 by
      exact quarticPolynomial_eval_firstConnectorMeshEndpoint 0]
  with_unfolding_all decide

theorem firstConnectorPreparedAmbientLeftLeThirteenEighths :
    firstConnectorCachedSource.preparedOwner.track.initial.ambientLeftClearance.bound ≤
      (13 / 8 : Q) := by
  rw [show firstConnectorCachedSource.preparedOwner =
      CCL.Riemann.PreparedSheetContinuation.prepared firstConnectorSegment
        CCL.Riemann.PreparedClearPathModels.zeroEndpoint
          firstConnectorStartOwner (firstConnectorEdgeRequest 0) by rfl,
    firstConnectorPreparedEqRecentered]
  exact firstConnectorRecenteredAmbientLeftLeThirteenEighths

def firstConnectorOwnerOne :=
  CCL.Riemann.PreparedSheetContinuation.advanceCached firstConnectorSegment
    firstConnectorSegment_withinAmbient
      CCL.Riemann.PreparedClearPathModels.zeroEndpoint firstConnectorStartOwner
        (firstConnectorEdgeRequest 0) firstConnectorCachedSource
          firstConnectorCanonicalSmall

theorem firstConnectorOwnerOneAmbientLeftLeThreeHalves :
    firstConnectorOwnerOne.track.initial.ambientLeftClearance.bound ≤
      (3 / 2 : Q) :=
  firstConnectorEdgeZeroAdvanceCache.ambientLeftQuarterSq.trans
    (quarterSquare_le_threeHalves_of_le_thirteenEighths _
      firstConnectorCachedSource.preparedOwner.track.initial.ambientLeftClearance.positive.le
      firstConnectorPreparedAmbientLeftLeThirteenEighths)

theorem firstConnectorOwnerOneBoxEq :
    firstConnectorOwnerOne.track.initial.box = firstConnectorBoxOne := by
  calc
    firstConnectorOwnerOne.track.initial.box =
        firstConnectorCachedSource.preparedOwner.track.initial.box :=
      firstConnectorEdgeZeroAdvanceCache.initialBox
    _ = (CCL.Riemann.PreparedSheetContinuation.recentered
        firstConnectorStartOwner).track.initial.box := by
      rw [show firstConnectorCachedSource.preparedOwner =
        CCL.Riemann.PreparedSheetContinuation.prepared firstConnectorSegment
          CCL.Riemann.PreparedClearPathModels.zeroEndpoint
            firstConnectorStartOwner (firstConnectorEdgeRequest 0) by rfl,
        firstConnectorPreparedEqRecentered]
    _ = firstConnectorBoxOne := by
      rw [firstConnectorRecenteredEq, firstConnectorMoving.ownerInitialBox,
        firstConnectorMovingBoxEq]

theorem firstConnectorOwnerOneAmbientEq :
    firstConnectorOwnerOne.ambient = firstConnectorBoxOne := by
  calc
    firstConnectorOwnerOne.ambient =
        firstConnectorCachedSource.preparedOwner.ambient :=
      firstConnectorEdgeZeroAdvanceCache.ambientBox
    _ = (CCL.Riemann.PreparedSheetContinuation.recentered
        firstConnectorStartOwner).ambient := by
      rw [show firstConnectorCachedSource.preparedOwner =
        CCL.Riemann.PreparedSheetContinuation.prepared firstConnectorSegment
          CCL.Riemann.PreparedClearPathModels.zeroEndpoint
            firstConnectorStartOwner (firstConnectorEdgeRequest 0) by rfl,
        firstConnectorPreparedEqRecentered]
    _ = firstConnectorBoxOne := by
      rw [firstConnectorRecenteredEq, firstConnectorMoving.ownerAmbientBox,
        firstConnectorMovingBoxEq]

/-! ## Same-box transport through grid endpoint two -/

theorem firstConnectorMeshVariationBounds (edge : Fin 8) :
    (39 / 64 : Q) ≤
        CCL.Riemann.ClearSheetContinuation.variationBound firstConnectorSegment
          (firstConnectorMeshEndpoint
            (firstConnectorEdgeSource edge)).parameter
          (firstConnectorMeshEndpoint
            (firstConnectorEdgeTarget edge)).parameter ∧
      CCL.Riemann.ClearSheetContinuation.variationBound firstConnectorSegment
          (firstConnectorMeshEndpoint
            (firstConnectorEdgeSource edge)).parameter
          (firstConnectorMeshEndpoint
            (firstConnectorEdgeTarget edge)).parameter < (40 / 64 : Q) := by
  rw [firstConnectorMeshEndpoint_parameter,
    firstConnectorMeshEndpoint_parameter]
  exact firstConnectorGridVariationBounds edge

theorem firstConnectorMeshVariationMargin (edge : Fin 8) : (1 / 2 : Q) ≤
    CCL.Riemann.ClearSheetContinuation.variationBound firstConnectorSegment
        (firstConnectorMeshEndpoint
          (firstConnectorEdgeSource edge)).parameter
        (firstConnectorMeshEndpoint
          (firstConnectorEdgeTarget edge)).parameter -
      RFAP.ConstructiveGaussian.Gaussian.normSq
        (CCL.Riemann.FinitePeriodExamples.quarticCurve.polynomial.eval
            (firstConnectorSegment.pointAt
              (firstConnectorMeshEndpoint
                (firstConnectorEdgeSource edge)).parameter) -
          CCL.Riemann.FinitePeriodExamples.quarticCurve.polynomial.eval
            (firstConnectorSegment.pointAt
              (firstConnectorMeshEndpoint
                (firstConnectorEdgeTarget edge)).parameter)) := by
  rw [firstConnectorMeshEndpoint_parameter,
    firstConnectorMeshEndpoint_parameter]
  change (1 / 2 : Q) ≤
    CCL.Riemann.ClearSheetContinuation.variationBound firstConnectorSegment
        (firstConnectorGridEndpoint
          (firstConnectorEdgeSource edge)).parameter
        (firstConnectorGridEndpoint
          (firstConnectorEdgeTarget edge)).parameter -
      RFAP.ConstructiveGaussian.Gaussian.normSq
        (CCL.Riemann.FinitePeriodExamples.quarticPolynomial.eval
            (firstConnectorSegment.pointAt
              (firstConnectorGridEndpoint
                (firstConnectorEdgeSource edge)).parameter) -
          CCL.Riemann.FinitePeriodExamples.quarticPolynomial.eval
            (firstConnectorSegment.pointAt
              (firstConnectorGridEndpoint
                (firstConnectorEdgeTarget edge)).parameter))
  rw [quarticPolynomial_eval_firstConnectorGridEndpoint,
    quarticPolynomial_eval_firstConnectorGridEndpoint]
  exact firstConnectorGridVariationMargin edge

private theorem fortyOver64EqFiveEighths : (40 / 64 : Q) = 5 / 8 := by
  have sixtyFourNonzero : (64 : Q) ≠ 0 := by
    simpa only [Nat.cast_ofNat] using (qNatPositive 64 (by omega)).ne'
  have eightNonzero : (8 : Q) ≠ 0 := by
    simpa only [Nat.cast_ofNat] using (qNatPositive 8 (by omega)).ne'
  apply RFAP.ConstructiveFraction.div_eq_div_of_cross_mul
    sixtyFourNonzero eightNonzero
  ring1

theorem fiveEighthsLeStrengthenFromDirectCache {parameter : Gaussian}
    (owner : CCL.Riemann.SquareRootContinuationChain.Owner parameter)
    (box : Box) (boxEq : owner.track.initial.box = box)
    (cache : DirectClearanceFiveEighths parameter box) : (5 / 8 : Q) ≤
      (CCL.Riemann.ExactQuadraticOwnerClearance.strengthenQuadraticOwner
        owner).track.initial.clearance.bound := by
  subst box
  calc
    (5 / 8 : Q) ≤ cache.clearance.bound := cache.fiveEighths_le
    _ = (CCL.Riemann.ExactQuadraticOwnerClearance.directBoundaryClearance
        parameter owner.track.initial.box cache.leftNonzero cache.rightNonzero
          cache.bottomNonzero cache.topNonzero).bound :=
      congrArg RFAP.BoxClearance.BoundaryClearance.bound cache.clearance_eq
    _ ≤ (CCL.Riemann.ExactQuadraticOwnerClearance.strengthenQuadraticOwner
        owner).track.initial.clearance.bound :=
      CCL.Riemann.ExactQuadraticOwnerClearance.directBoundaryClearance_le_strengthenQuadraticOwner
        owner
          cache.leftNonzero cache.rightNonzero cache.bottomNonzero
            cache.topNonzero

theorem preparedAmbientLeftLeThreeHalvesFromDirectCache
    (current : CCL.Riemann.PreparedSheetContinuation.Endpoint)
    (owner : CCL.Riemann.SquareRootContinuationChain.Owner
      (CCL.Riemann.FinitePeriodExamples.quarticCurve.polynomial.eval
        (firstConnectorSegment.pointAt current.parameter)))
    (request : CCL.Riemann.PreparedSheetContinuation.StepRequest)
    (ready : CCL.Riemann.PreparedSheetContinuation.AlreadyPrepared
      firstConnectorSegment current owner request)
    (strengthenedCarries :
      CCL.Riemann.ClearSheetContinuation.variationBound firstConnectorSegment
          current.parameter request.endpoint.parameter <
        (CCL.Riemann.ExactQuadraticOwnerClearance.strengthenQuadraticOwner
          owner).track.initial.clearance.bound)
    (dominance :
      CCL.Riemann.ExactQuadraticOwnerClearance.AmbientClearanceDominance owner)
    (ambientLeftLeThreeHalves :
      owner.track.initial.ambientLeftClearance.bound ≤ (3 / 2 : Q))
    (box : Box) (boxEq : owner.track.initial.box = box)
    (cache : DirectClearanceFiveEighths
      (CCL.Riemann.FinitePeriodExamples.quarticCurve.polynomial.eval
        (firstConnectorSegment.pointAt current.parameter)) box) :
    (CCL.Riemann.PreparedSheetContinuation.prepared firstConnectorSegment
      current owner request).track.initial.ambientLeftClearance.bound ≤
        (3 / 2 : Q) := by
  subst box
  let ownerLeftNonzero :
      CCL.Riemann.SquareRootContinuationChain.Owner.verticalDeterminant
        (CCL.Riemann.FinitePeriodExamples.quarticCurve.polynomial.eval
          (firstConnectorSegment.pointAt current.parameter))
          owner.track.initial.box.xLower ≠ 0 := by
    exact cache.leftNonzero
  let ownerRightNonzero :
      CCL.Riemann.SquareRootContinuationChain.Owner.verticalDeterminant
        (CCL.Riemann.FinitePeriodExamples.quarticCurve.polynomial.eval
          (firstConnectorSegment.pointAt current.parameter))
          owner.track.initial.box.xUpper ≠ 0 := by
    exact cache.rightNonzero
  let ownerBottomNonzero :
      CCL.Riemann.SquareRootContinuationChain.Owner.horizontalDeterminant
        (CCL.Riemann.FinitePeriodExamples.quarticCurve.polynomial.eval
          (firstConnectorSegment.pointAt current.parameter))
          owner.track.initial.box.yLower ≠ 0 := by
    exact cache.bottomNonzero
  let ownerTopNonzero :
      CCL.Riemann.SquareRootContinuationChain.Owner.horizontalDeterminant
        (CCL.Riemann.FinitePeriodExamples.quarticCurve.polynomial.eval
          (firstConnectorSegment.pointAt current.parameter))
          owner.track.initial.box.yUpper ≠ 0 := by
    exact cache.topNonzero
  have directUpper :
      (CCL.Riemann.ExactQuadraticOwnerClearance.directBoundaryClearance
        (CCL.Riemann.FinitePeriodExamples.quarticCurve.polynomial.eval
          (firstConnectorSegment.pointAt current.parameter))
        owner.track.initial.box ownerLeftNonzero ownerRightNonzero
          ownerBottomNonzero ownerTopNonzero).bound ≤ (3 / 2 : Q) := by
    rw [CCL.Riemann.ExactQuadraticOwnerClearance.directBoundaryClearance_bound]
    exact cache.directBound_le_threeHalves
  by_cases carries :
      CCL.Riemann.ClearSheetContinuation.variationBound firstConnectorSegment
          current.parameter request.endpoint.parameter <
        owner.track.initial.clearance.bound
  · rw [CCL.Riemann.PreparedSheetContinuation.prepared_eq_self_of_ready
      firstConnectorSegment current owner request ready carries]
    exact ambientLeftLeThreeHalves
  · rw [CCL.Riemann.PreparedSheetContinuation.prepared_eq_strengthenQuadraticOwner_of_ready
      firstConnectorSegment current owner request ready carries
        strengthenedCarries]
    rcases
      CCL.Riemann.ExactQuadraticOwnerClearance.strengthenQuadraticOwner_ambient_clearance_eq
        owner ownerLeftNonzero ownerRightNonzero ownerBottomNonzero
          ownerTopNonzero with ⟨leftEq, _, _, _⟩
    rw [leftEq,
      CCL.Riemann.ExactQuadraticOwnerClearance.strengthenQuadraticOwner_clearance_eq_max
        owner ownerLeftNonzero ownerRightNonzero ownerBottomNonzero
          ownerTopNonzero]
    exact max_le
      (dominance.left.trans ambientLeftLeThreeHalves)
      directUpper

theorem firstConnectorOwnerOneReady :
    CCL.Riemann.PreparedSheetContinuation.AlreadyPrepared firstConnectorSegment
      (firstConnectorEdgeRequest 0).endpoint firstConnectorOwnerOne
        (firstConnectorEdgeRequest 1) := by
  refine ⟨?_, ?_, ?_⟩
  · rw [firstConnectorOwnerOneBoxEq]
    with_unfolding_all decide
  · exact
      (CCL.Riemann.UniformSquareRootPreparation.predictedClearance_le_transportFloor
        firstConnectorSegment
          (firstConnectorEdgeRequest 1).rootDiameter
          (firstConnectorEdgeRequest 1).rootDiameterPositive
            firstConnectorDerivativeMarginLe).trans
        firstConnectorEdgeZeroAdvanceCache.clearanceFloor
  · rw [firstConnectorOwnerOneBoxEq]
    change
      -CCL.Riemann.UniformSquareRootPreparation.rootAmbientRadius
          firstConnectorSegment ≤ firstConnectorBoxOne.xLower ∧
        firstConnectorBoxOne.xUpper ≤
          CCL.Riemann.UniformSquareRootPreparation.rootAmbientRadius
            firstConnectorSegment ∧
        -CCL.Riemann.UniformSquareRootPreparation.rootAmbientRadius
          firstConnectorSegment ≤ firstConnectorBoxOne.yLower ∧
        firstConnectorBoxOne.yUpper ≤
          CCL.Riemann.UniformSquareRootPreparation.rootAmbientRadius
            firstConnectorSegment
    have threeLe :=
      CCL.Riemann.UniformSquareRootPreparation.three_le_rootAmbientRadius
        firstConnectorSegment
    exact ⟨(RFAP.ConstructiveFraction.neg_le_neg_direct threeLe).trans
        (by with_unfolding_all decide),
      (by with_unfolding_all decide :
        firstConnectorBoxOne.xUpper ≤ (3 : Q)).trans threeLe,
      (RFAP.ConstructiveFraction.neg_le_neg_direct threeLe).trans
        (by with_unfolding_all decide),
      (by with_unfolding_all decide :
        firstConnectorBoxOne.yUpper ≤ (3 : Q)).trans threeLe⟩

theorem firstConnectorOwnerOneStrengthenedCarries :
    CCL.Riemann.ClearSheetContinuation.variationBound firstConnectorSegment
        (firstConnectorEdgeRequest 0).endpoint.parameter
          (firstConnectorEdgeRequest 1).endpoint.parameter <
      (CCL.Riemann.ExactQuadraticOwnerClearance.strengthenQuadraticOwner
        firstConnectorOwnerOne).track.initial.clearance.bound := by
  have parameterEq :
      CCL.Riemann.FinitePeriodExamples.quarticCurve.polynomial.eval
          (firstConnectorSegment.pointAt
            (firstConnectorEdgeRequest 0).endpoint.parameter) =
        firstConnectorGridParameter 1 :=
    quarticPolynomial_eval_firstConnectorMeshEndpoint 1
  let cache : DirectClearanceFiveEighths
      (CCL.Riemann.FinitePeriodExamples.quarticCurve.polynomial.eval
        (firstConnectorSegment.pointAt
          (firstConnectorEdgeRequest 0).endpoint.parameter))
        firstConnectorBoxOne := by
    rw [parameterEq]
    exact firstConnectorBoxOneClearance 0
  exact (firstConnectorMeshVariationBounds 1).2.trans_eq
    fortyOver64EqFiveEighths |>.trans_le
      (fiveEighthsLeStrengthenFromDirectCache firstConnectorOwnerOne
        firstConnectorBoxOne firstConnectorOwnerOneBoxEq cache)

theorem firstConnectorOwnerOneCanonicalSmall :
    CCL.Riemann.ClearSheetContinuation.variationBound firstConnectorSegment
        (firstConnectorEdgeRequest 0).endpoint.parameter
          (firstConnectorEdgeRequest 1).endpoint.parameter <
      (CCL.Riemann.PreparedSheetContinuation.prepared firstConnectorSegment
        (firstConnectorEdgeRequest 0).endpoint firstConnectorOwnerOne
          (firstConnectorEdgeRequest 1)).track.initial.clearance.bound :=
  CCL.Riemann.PreparedSheetContinuation.variation_lt_prepared_of_ready_of_strengthenedCarries
    firstConnectorSegment
      (firstConnectorEdgeRequest 0).endpoint firstConnectorOwnerOne
        (firstConnectorEdgeRequest 1) firstConnectorOwnerOneReady
          firstConnectorOwnerOneStrengthenedCarries

def firstConnectorOwnerOneCachedSource :=
  CCL.Riemann.PreparedSheetContinuation.CachedSource.canonical
    firstConnectorSegment (firstConnectorEdgeRequest 0).endpoint
      firstConnectorOwnerOne (firstConnectorEdgeRequest 1)

theorem firstConnectorOwnerOnePreparedDominance :
    CCL.Riemann.ExactQuadraticOwnerClearance.AmbientClearanceDominance
      firstConnectorOwnerOneCachedSource.preparedOwner :=
  CCL.Riemann.PreparedSheetContinuation.prepared_ambientClearanceDominance_of_ready_of_strengthenedCarries
      firstConnectorSegment (firstConnectorEdgeRequest 0).endpoint
        firstConnectorOwnerOne (firstConnectorEdgeRequest 1)
          firstConnectorOwnerOneReady firstConnectorOwnerOneStrengthenedCarries
            firstConnectorEdgeZeroAdvanceCache.dominance

theorem firstConnectorOwnerOnePreparedBudget :
    CCL.Riemann.ExactQuadraticOwnerClearance.QuadraticAmbientBudget
      firstConnectorOwnerOneCachedSource.preparedOwner :=
  CCL.Riemann.PreparedSheetContinuation.prepared_quadraticAmbientBudget_of_ready_of_strengthenedCarries
      firstConnectorSegment (firstConnectorEdgeRequest 0).endpoint
        firstConnectorOwnerOne (firstConnectorEdgeRequest 1)
          firstConnectorOwnerOneReady firstConnectorOwnerOneStrengthenedCarries
            firstConnectorEdgeZeroAdvanceCache.budget

theorem firstConnectorOwnerOnePreparedAmbientLeftLeThreeHalves :
    firstConnectorOwnerOneCachedSource.preparedOwner.track.initial.ambientLeftClearance.bound ≤
      (3 / 2 : Q) := by
  have parameterEq :
      CCL.Riemann.FinitePeriodExamples.quarticCurve.polynomial.eval
          (firstConnectorSegment.pointAt
            (firstConnectorEdgeRequest 0).endpoint.parameter) =
        firstConnectorGridParameter 1 :=
    quarticPolynomial_eval_firstConnectorMeshEndpoint 1
  let cache : DirectClearanceFiveEighths
      (CCL.Riemann.FinitePeriodExamples.quarticCurve.polynomial.eval
        (firstConnectorSegment.pointAt
          (firstConnectorEdgeRequest 0).endpoint.parameter))
        firstConnectorBoxOne := by
    rw [parameterEq]
    exact firstConnectorBoxOneClearance 0
  change
    (CCL.Riemann.PreparedSheetContinuation.prepared firstConnectorSegment
      (firstConnectorEdgeRequest 0).endpoint firstConnectorOwnerOne
        (firstConnectorEdgeRequest 1)).track.initial.ambientLeftClearance.bound ≤
      (3 / 2 : Q)
  exact preparedAmbientLeftLeThreeHalvesFromDirectCache
    (firstConnectorEdgeRequest 0).endpoint firstConnectorOwnerOne
      (firstConnectorEdgeRequest 1) firstConnectorOwnerOneReady
        firstConnectorOwnerOneStrengthenedCarries
          firstConnectorEdgeZeroAdvanceCache.dominance
            firstConnectorOwnerOneAmbientLeftLeThreeHalves
              firstConnectorBoxOne firstConnectorOwnerOneBoxEq cache

theorem firstConnectorOwnerOnePreparedMargin : (1 / 2 : Q) ≤
    firstConnectorOwnerOneCachedSource.preparedOwner.track.initial.clearance.bound -
      RFAP.ConstructiveGaussian.Gaussian.normSq
        (CCL.Riemann.FinitePeriodExamples.quarticCurve.polynomial.eval
            (firstConnectorSegment.pointAt
              (firstConnectorEdgeRequest 0).endpoint.parameter) -
          CCL.Riemann.FinitePeriodExamples.quarticCurve.polynomial.eval
            (firstConnectorSegment.pointAt
              (firstConnectorEdgeRequest 1).endpoint.parameter)) :=
  CCL.Riemann.PreparedSheetContinuation.prepared_margin_lower_of_ready_of_strengthenedCarries
    firstConnectorSegment
      (firstConnectorEdgeRequest 0).endpoint firstConnectorOwnerOne
        (firstConnectorEdgeRequest 1) firstConnectorOwnerOneReady
          firstConnectorOwnerOneStrengthenedCarries (1 / 2) _
            (firstConnectorMeshVariationMargin 1)

theorem firstConnectorEdgeOneAdvanceCache :
    CCL.Riemann.PreparedSheetContinuation.QuadraticAdvanceCache
      firstConnectorSegment firstConnectorSegment_withinAmbient
        (firstConnectorEdgeRequest 0).endpoint firstConnectorOwnerOne
          (firstConnectorEdgeRequest 1) firstConnectorOwnerOneCachedSource
            firstConnectorOwnerOneCanonicalSmall := by
  apply CCL.Riemann.PreparedSheetContinuation.quadraticAdvanceCache
  · rw [show
      CCL.Riemann.FinitePeriodExamples.quarticCurve.polynomial.eval
          (firstConnectorSegment.pointAt
            (firstConnectorEdgeRequest 0).endpoint.parameter) =
        firstConnectorGridParameter 1 by
          exact quarticPolynomial_eval_firstConnectorMeshEndpoint 1,
      show
      CCL.Riemann.FinitePeriodExamples.quarticCurve.polynomial.eval
          (firstConnectorSegment.pointAt
            (firstConnectorEdgeRequest 1).endpoint.parameter) =
        firstConnectorGridParameter 2 by
          exact quarticPolynomial_eval_firstConnectorMeshEndpoint 2]
    exact firstConnectorAdjacentParametersDifferent 1
  · exact firstConnectorDerivativeMarginLe
  · exact firstConnectorOwnerOnePreparedDominance
  · exact firstConnectorOwnerOnePreparedMargin
  · exact firstConnectorOwnerOnePreparedBudget
  · rw [show
      CCL.Riemann.FinitePeriodExamples.quarticCurve.polynomial.eval
          (firstConnectorSegment.pointAt
            (firstConnectorEdgeRequest 1).endpoint.parameter) =
        firstConnectorGridParameter 2 by
          exact quarticPolynomial_eval_firstConnectorMeshEndpoint 2]
    exact firstConnectorGridParameterNormSqLe 2

def firstConnectorOwnerTwo :=
  CCL.Riemann.PreparedSheetContinuation.advanceCached firstConnectorSegment
    firstConnectorSegment_withinAmbient (firstConnectorEdgeRequest 0).endpoint
      firstConnectorOwnerOne (firstConnectorEdgeRequest 1)
        firstConnectorOwnerOneCachedSource firstConnectorOwnerOneCanonicalSmall

theorem firstConnectorOwnerTwoAmbientLeftLeNineSixteenths :
    firstConnectorOwnerTwo.track.initial.ambientLeftClearance.bound ≤
      (9 / 16 : Q) :=
  firstConnectorEdgeOneAdvanceCache.ambientLeftQuarterSq.trans
    (quarterSquare_le_nineSixteenths _
      firstConnectorOwnerOneCachedSource.preparedOwner.track.initial.ambientLeftClearance.positive.le
      firstConnectorOwnerOnePreparedAmbientLeftLeThreeHalves)

theorem firstConnectorOwnerTwoBoxEq :
    firstConnectorOwnerTwo.track.initial.box = firstConnectorBoxOne := by
  calc
    firstConnectorOwnerTwo.track.initial.box =
        firstConnectorOwnerOneCachedSource.preparedOwner.track.initial.box :=
      firstConnectorEdgeOneAdvanceCache.initialBox
    _ = firstConnectorOwnerOne.track.initial.box :=
      CCL.Riemann.PreparedSheetContinuation.prepared_initial_box_eq_of_ready_of_strengthenedCarries
          firstConnectorSegment (firstConnectorEdgeRequest 0).endpoint
            firstConnectorOwnerOne (firstConnectorEdgeRequest 1)
              firstConnectorOwnerOneReady
                firstConnectorOwnerOneStrengthenedCarries
    _ = firstConnectorBoxOne := firstConnectorOwnerOneBoxEq

/-! ## Reusable same-box edge certificates -/

structure SameBoxStep (edge : Fin 8)
    (owner : CCL.Riemann.SquareRootContinuationChain.Owner
      (CCL.Riemann.FinitePeriodExamples.quarticCurve.polynomial.eval
        (firstConnectorSegment.pointAt
          (firstConnectorMeshEndpoint
            (firstConnectorEdgeSource edge)).parameter))) where
  ready : CCL.Riemann.PreparedSheetContinuation.AlreadyPrepared
    firstConnectorSegment
      (firstConnectorMeshEndpoint (firstConnectorEdgeSource edge)) owner
        (firstConnectorEdgeRequest edge)
  strengthenedCarries :
    CCL.Riemann.ClearSheetContinuation.variationBound firstConnectorSegment
        (firstConnectorMeshEndpoint
          (firstConnectorEdgeSource edge)).parameter
        (firstConnectorEdgeRequest edge).endpoint.parameter <
      (CCL.Riemann.ExactQuadraticOwnerClearance.strengthenQuadraticOwner
        owner).track.initial.clearance.bound
  canonicalSmall :
    CCL.Riemann.ClearSheetContinuation.variationBound firstConnectorSegment
        (firstConnectorMeshEndpoint
          (firstConnectorEdgeSource edge)).parameter
        (firstConnectorEdgeRequest edge).endpoint.parameter <
      (CCL.Riemann.PreparedSheetContinuation.prepared firstConnectorSegment
        (firstConnectorMeshEndpoint (firstConnectorEdgeSource edge)) owner
          (firstConnectorEdgeRequest edge)).track.initial.clearance.bound
  preparedAmbientLeftLeThreeHalves :
    (CCL.Riemann.PreparedSheetContinuation.CachedSource.canonical
      firstConnectorSegment
        (firstConnectorMeshEndpoint (firstConnectorEdgeSource edge)) owner
          (firstConnectorEdgeRequest edge)).preparedOwner.track.initial.ambientLeftClearance.bound ≤
      (3 / 2 : Q)
  advanceCache : CCL.Riemann.PreparedSheetContinuation.QuadraticAdvanceCache
    firstConnectorSegment firstConnectorSegment_withinAmbient
      (firstConnectorMeshEndpoint (firstConnectorEdgeSource edge)) owner
        (firstConnectorEdgeRequest edge)
          (CCL.Riemann.PreparedSheetContinuation.CachedSource.canonical
            firstConnectorSegment
              (firstConnectorMeshEndpoint (firstConnectorEdgeSource edge))
                owner (firstConnectorEdgeRequest edge)) canonicalSmall
  nextAmbientLeftLeNineSixteenths :
    (CCL.Riemann.PreparedSheetContinuation.advanceCached firstConnectorSegment
      firstConnectorSegment_withinAmbient
        (firstConnectorMeshEndpoint (firstConnectorEdgeSource edge)) owner
          (firstConnectorEdgeRequest edge)
            (CCL.Riemann.PreparedSheetContinuation.CachedSource.canonical
              firstConnectorSegment
                (firstConnectorMeshEndpoint (firstConnectorEdgeSource edge))
                  owner (firstConnectorEdgeRequest edge)) canonicalSmall).track.initial.ambientLeftClearance.bound ≤
      (9 / 16 : Q)

theorem sameBoxStep (edge : Fin 8)
    (owner : CCL.Riemann.SquareRootContinuationChain.Owner
      (CCL.Riemann.FinitePeriodExamples.quarticCurve.polynomial.eval
        (firstConnectorSegment.pointAt
          (firstConnectorMeshEndpoint
            (firstConnectorEdgeSource edge)).parameter)))
    (box : Box) (boxEq : owner.track.initial.box = box)
    (boxSmall : box.diagonalSq < (firstConnectorEdgeRequest edge).rootDiameter)
    (boxRefines : box.Refines
      (CCL.Riemann.UniformSquareRootPreparation.rootAmbient
        firstConnectorSegment))
    (clearanceFloor :
      CCL.Riemann.ExactQuadraticOwnerClearance.quadraticAmbientTransportFloor ≤
        owner.track.initial.clearance.bound)
    (dominance :
      CCL.Riemann.ExactQuadraticOwnerClearance.AmbientClearanceDominance owner)
    (budget :
      CCL.Riemann.ExactQuadraticOwnerClearance.QuadraticAmbientBudget owner)
    (ambientLeftLeThreeHalves :
      owner.track.initial.ambientLeftClearance.bound ≤ (3 / 2 : Q))
    (directCache : DirectClearanceFiveEighths
      (firstConnectorGridParameter (firstConnectorEdgeSource edge)) box) :
    SameBoxStep edge owner := by
  have ready : CCL.Riemann.PreparedSheetContinuation.AlreadyPrepared
      firstConnectorSegment
        (firstConnectorMeshEndpoint (firstConnectorEdgeSource edge)) owner
          (firstConnectorEdgeRequest edge) := by
    refine ⟨?_, ?_, ?_⟩
    · rw [boxEq]
      exact boxSmall
    · exact
        (CCL.Riemann.UniformSquareRootPreparation.predictedClearance_le_transportFloor
          firstConnectorSegment (firstConnectorEdgeRequest edge).rootDiameter
            (firstConnectorEdgeRequest edge).rootDiameterPositive
              firstConnectorDerivativeMarginLe).trans clearanceFloor
    · rw [boxEq]
      exact boxRefines
  have parameterEq :
      CCL.Riemann.FinitePeriodExamples.quarticCurve.polynomial.eval
          (firstConnectorSegment.pointAt
            (firstConnectorMeshEndpoint
              (firstConnectorEdgeSource edge)).parameter) =
        firstConnectorGridParameter (firstConnectorEdgeSource edge) :=
    quarticPolynomial_eval_firstConnectorMeshEndpoint _
  let actualCache : DirectClearanceFiveEighths
      (CCL.Riemann.FinitePeriodExamples.quarticCurve.polynomial.eval
        (firstConnectorSegment.pointAt
          (firstConnectorMeshEndpoint
            (firstConnectorEdgeSource edge)).parameter)) box := by
    rw [parameterEq]
    exact directCache
  have strengthenedCarries :
      CCL.Riemann.ClearSheetContinuation.variationBound firstConnectorSegment
          (firstConnectorMeshEndpoint
            (firstConnectorEdgeSource edge)).parameter
          (firstConnectorEdgeRequest edge).endpoint.parameter <
        (CCL.Riemann.ExactQuadraticOwnerClearance.strengthenQuadraticOwner
          owner).track.initial.clearance.bound := by
    exact (firstConnectorMeshVariationBounds edge).2.trans_eq
      fortyOver64EqFiveEighths |>.trans_le
        (fiveEighthsLeStrengthenFromDirectCache owner box boxEq actualCache)
  have canonicalSmall :=
    CCL.Riemann.PreparedSheetContinuation.variation_lt_prepared_of_ready_of_strengthenedCarries
        firstConnectorSegment
          (firstConnectorMeshEndpoint (firstConnectorEdgeSource edge)) owner
            (firstConnectorEdgeRequest edge) ready strengthenedCarries
  let cached := CCL.Riemann.PreparedSheetContinuation.CachedSource.canonical
    firstConnectorSegment
      (firstConnectorMeshEndpoint (firstConnectorEdgeSource edge)) owner
        (firstConnectorEdgeRequest edge)
  have preparedDominance :
      CCL.Riemann.ExactQuadraticOwnerClearance.AmbientClearanceDominance
        cached.preparedOwner :=
    CCL.Riemann.PreparedSheetContinuation.prepared_ambientClearanceDominance_of_ready_of_strengthenedCarries
        firstConnectorSegment
          (firstConnectorMeshEndpoint (firstConnectorEdgeSource edge)) owner
            (firstConnectorEdgeRequest edge) ready strengthenedCarries dominance
  have preparedBudget :
      CCL.Riemann.ExactQuadraticOwnerClearance.QuadraticAmbientBudget
        cached.preparedOwner :=
    CCL.Riemann.PreparedSheetContinuation.prepared_quadraticAmbientBudget_of_ready_of_strengthenedCarries
        firstConnectorSegment
          (firstConnectorMeshEndpoint (firstConnectorEdgeSource edge)) owner
            (firstConnectorEdgeRequest edge) ready strengthenedCarries budget
  have preparedAmbientLeftLeThreeHalves :
      cached.preparedOwner.track.initial.ambientLeftClearance.bound ≤
        (3 / 2 : Q) := by
    change
      (CCL.Riemann.PreparedSheetContinuation.prepared firstConnectorSegment
        (firstConnectorMeshEndpoint (firstConnectorEdgeSource edge)) owner
          (firstConnectorEdgeRequest edge)).track.initial.ambientLeftClearance.bound ≤
            (3 / 2 : Q)
    exact preparedAmbientLeftLeThreeHalvesFromDirectCache
      (firstConnectorMeshEndpoint (firstConnectorEdgeSource edge)) owner
        (firstConnectorEdgeRequest edge) ready strengthenedCarries dominance
          ambientLeftLeThreeHalves box boxEq actualCache
  have preparedMargin : (1 / 2 : Q) ≤
      cached.preparedOwner.track.initial.clearance.bound -
        RFAP.ConstructiveGaussian.Gaussian.normSq
          (CCL.Riemann.FinitePeriodExamples.quarticCurve.polynomial.eval
              (firstConnectorSegment.pointAt
                (firstConnectorMeshEndpoint
                  (firstConnectorEdgeSource edge)).parameter) -
            CCL.Riemann.FinitePeriodExamples.quarticCurve.polynomial.eval
              (firstConnectorSegment.pointAt
                (firstConnectorEdgeRequest edge).endpoint.parameter)) :=
    CCL.Riemann.PreparedSheetContinuation.prepared_margin_lower_of_ready_of_strengthenedCarries
        firstConnectorSegment
          (firstConnectorMeshEndpoint (firstConnectorEdgeSource edge)) owner
            (firstConnectorEdgeRequest edge) ready strengthenedCarries
              (1 / 2) _ (firstConnectorMeshVariationMargin edge)
  have different :
      CCL.Riemann.FinitePeriodExamples.quarticCurve.polynomial.eval
          (firstConnectorSegment.pointAt
            (firstConnectorMeshEndpoint
              (firstConnectorEdgeSource edge)).parameter) ≠
        CCL.Riemann.FinitePeriodExamples.quarticCurve.polynomial.eval
          (firstConnectorSegment.pointAt
            (firstConnectorEdgeRequest edge).endpoint.parameter) := by
    change CCL.Riemann.FinitePeriodExamples.quarticPolynomial.eval
        (firstConnectorSegment.pointAt
          (firstConnectorMeshEndpoint
            (firstConnectorEdgeSource edge)).parameter) ≠
      CCL.Riemann.FinitePeriodExamples.quarticPolynomial.eval
        (firstConnectorSegment.pointAt
          (firstConnectorMeshEndpoint
            (firstConnectorEdgeTarget edge)).parameter)
    rw [quarticPolynomial_eval_firstConnectorMeshEndpoint,
      quarticPolynomial_eval_firstConnectorMeshEndpoint]
    exact firstConnectorAdjacentParametersDifferent edge
  have targetNorm : RFAP.ConstructiveGaussian.Gaussian.normSq
      (CCL.Riemann.FinitePeriodExamples.quarticCurve.polynomial.eval
        (firstConnectorSegment.pointAt
          (firstConnectorEdgeRequest edge).endpoint.parameter)) ≤ (256 : Q) := by
    change RFAP.ConstructiveGaussian.Gaussian.normSq
      (CCL.Riemann.FinitePeriodExamples.quarticPolynomial.eval
        (firstConnectorSegment.pointAt
          (firstConnectorMeshEndpoint
            (firstConnectorEdgeTarget edge)).parameter)) ≤ (256 : Q)
    rw [quarticPolynomial_eval_firstConnectorMeshEndpoint]
    exact firstConnectorGridParameterNormSqLe
      (firstConnectorEdgeTarget edge)
  have advanceCache :
      CCL.Riemann.PreparedSheetContinuation.QuadraticAdvanceCache
        firstConnectorSegment firstConnectorSegment_withinAmbient
          (firstConnectorMeshEndpoint (firstConnectorEdgeSource edge)) owner
            (firstConnectorEdgeRequest edge) cached canonicalSmall := by
    apply CCL.Riemann.PreparedSheetContinuation.quadraticAdvanceCache
    · exact different
    · exact firstConnectorDerivativeMarginLe
    · exact preparedDominance
    · exact preparedMargin
    · exact preparedBudget
    · exact targetNorm
  have nextAmbientLeftLeNineSixteenths :=
    advanceCache.ambientLeftQuarterSq.trans
      (quarterSquare_le_nineSixteenths _
        cached.preparedOwner.track.initial.ambientLeftClearance.positive.le
          preparedAmbientLeftLeThreeHalves)
  exact ⟨ready, strengthenedCarries, canonicalSmall,
    preparedAmbientLeftLeThreeHalves, advanceCache,
      nextAmbientLeftLeNineSixteenths⟩

namespace SameBoxStep

def nextOwner {edge : Fin 8}
    {owner : CCL.Riemann.SquareRootContinuationChain.Owner
      (CCL.Riemann.FinitePeriodExamples.quarticCurve.polynomial.eval
        (firstConnectorSegment.pointAt
          (firstConnectorMeshEndpoint
            (firstConnectorEdgeSource edge)).parameter))}
    (step : SameBoxStep edge owner) :=
  CCL.Riemann.PreparedSheetContinuation.advanceCached firstConnectorSegment
    firstConnectorSegment_withinAmbient
      (firstConnectorMeshEndpoint (firstConnectorEdgeSource edge)) owner
        (firstConnectorEdgeRequest edge)
          (CCL.Riemann.PreparedSheetContinuation.CachedSource.canonical
            firstConnectorSegment
              (firstConnectorMeshEndpoint (firstConnectorEdgeSource edge))
                owner (firstConnectorEdgeRequest edge)) step.canonicalSmall

theorem nextOwnerBoxEq {edge : Fin 8}
    {owner : CCL.Riemann.SquareRootContinuationChain.Owner
      (CCL.Riemann.FinitePeriodExamples.quarticCurve.polynomial.eval
        (firstConnectorSegment.pointAt
          (firstConnectorMeshEndpoint
            (firstConnectorEdgeSource edge)).parameter))}
    (step : SameBoxStep edge owner) (box : Box)
    (boxEq : owner.track.initial.box = box) :
    step.nextOwner.track.initial.box = box := by
  calc
    step.nextOwner.track.initial.box =
        (CCL.Riemann.PreparedSheetContinuation.CachedSource.canonical
          firstConnectorSegment
            (firstConnectorMeshEndpoint (firstConnectorEdgeSource edge)) owner
              (firstConnectorEdgeRequest edge)).preparedOwner.track.initial.box :=
      step.advanceCache.initialBox
    _ = owner.track.initial.box :=
      CCL.Riemann.PreparedSheetContinuation.prepared_initial_box_eq_of_ready_of_strengthenedCarries
          firstConnectorSegment
            (firstConnectorMeshEndpoint (firstConnectorEdgeSource edge)) owner
              (firstConnectorEdgeRequest edge) step.ready
                step.strengthenedCarries
    _ = box := boxEq

end SameBoxStep

private theorem firstConnectorBoxOneSmall (edge : Fin 8) :
    firstConnectorBoxOne.diagonalSq <
      (firstConnectorEdgeRequest edge).rootDiameter := by
  change firstConnectorBoxOne.diagonalSq < workingRootDiameter
  with_unfolding_all decide

private theorem firstConnectorBoxOneRefines :
    firstConnectorBoxOne.Refines
      (CCL.Riemann.UniformSquareRootPreparation.rootAmbient
        firstConnectorSegment) := by
  change
    -CCL.Riemann.UniformSquareRootPreparation.rootAmbientRadius
        firstConnectorSegment ≤ firstConnectorBoxOne.xLower ∧
      firstConnectorBoxOne.xUpper ≤
        CCL.Riemann.UniformSquareRootPreparation.rootAmbientRadius
          firstConnectorSegment ∧
      -CCL.Riemann.UniformSquareRootPreparation.rootAmbientRadius
        firstConnectorSegment ≤ firstConnectorBoxOne.yLower ∧
      firstConnectorBoxOne.yUpper ≤
        CCL.Riemann.UniformSquareRootPreparation.rootAmbientRadius
          firstConnectorSegment
  have threeLe :=
    CCL.Riemann.UniformSquareRootPreparation.three_le_rootAmbientRadius
      firstConnectorSegment
  exact ⟨(RFAP.ConstructiveFraction.neg_le_neg_direct threeLe).trans
      (by with_unfolding_all decide),
    (by with_unfolding_all decide :
      firstConnectorBoxOne.xUpper ≤ (3 : Q)).trans threeLe,
    (RFAP.ConstructiveFraction.neg_le_neg_direct threeLe).trans
      (by with_unfolding_all decide),
    (by with_unfolding_all decide :
      firstConnectorBoxOne.yUpper ≤ (3 : Q)).trans threeLe⟩

theorem firstConnectorEdgeTwoStep : SameBoxStep 2 firstConnectorOwnerTwo :=
  sameBoxStep 2 firstConnectorOwnerTwo firstConnectorBoxOne
    firstConnectorOwnerTwoBoxEq (firstConnectorBoxOneSmall 2)
      firstConnectorBoxOneRefines firstConnectorEdgeOneAdvanceCache.clearanceFloor
        firstConnectorEdgeOneAdvanceCache.dominance
          firstConnectorEdgeOneAdvanceCache.budget
            (firstConnectorOwnerTwoAmbientLeftLeNineSixteenths.trans
              (by decide))
              (firstConnectorBoxOneClearance 1)

def firstConnectorOwnerThree := firstConnectorEdgeTwoStep.nextOwner

theorem firstConnectorOwnerThreeBoxEq :
    firstConnectorOwnerThree.track.initial.box = firstConnectorBoxOne :=
  firstConnectorEdgeTwoStep.nextOwnerBoxEq firstConnectorBoxOne
    firstConnectorOwnerTwoBoxEq

theorem firstConnectorEdgeThreeStep : SameBoxStep 3 firstConnectorOwnerThree :=
  sameBoxStep 3 firstConnectorOwnerThree firstConnectorBoxOne
    firstConnectorOwnerThreeBoxEq (firstConnectorBoxOneSmall 3)
      firstConnectorBoxOneRefines firstConnectorEdgeTwoStep.advanceCache.clearanceFloor
        firstConnectorEdgeTwoStep.advanceCache.dominance
          firstConnectorEdgeTwoStep.advanceCache.budget
            (firstConnectorEdgeTwoStep.nextAmbientLeftLeNineSixteenths.trans
              (by decide))
              (firstConnectorBoxOneClearance 2)

def firstConnectorOwnerFour := firstConnectorEdgeThreeStep.nextOwner

theorem firstConnectorOwnerFourBoxEq :
    firstConnectorOwnerFour.track.initial.box = firstConnectorBoxOne :=
  firstConnectorEdgeThreeStep.nextOwnerBoxEq firstConnectorBoxOne
    firstConnectorOwnerThreeBoxEq

theorem firstConnectorEndpointFourParameterEq :
    (firstConnectorEdgeRequest 3).endpoint.parameter =
      (firstConnectorMeshEndpoint 4).parameter := rfl

theorem quarticPolynomial_eval_firstConnectorEndpointFour :
    CCL.Riemann.FinitePeriodExamples.quarticCurve.polynomial.eval
        (firstConnectorSegment.pointAt
          (firstConnectorEdgeRequest 3).endpoint.parameter) =
      firstConnectorGridParameter 4 := by
  rw [firstConnectorEndpointFourParameterEq]
  exact quarticPolynomial_eval_firstConnectorMeshEndpoint 4

private theorem nineSixteenthsLeThirtyNineSixtyFour :
    (9 / 16 : Q) ≤ 39 / 64 := by
  apply divLeDivOfCrossMul (qNatPositive 16 (by omega))
    (qNatPositive 64 (by omega))
  calc
    (9 : Q) * 64 = 576 := by ring1
    _ ≤ 624 := RFAP.ConstructiveFraction.natCast_le_direct (by decide)
    _ = 39 * 16 := by ring1

structure DirectClearanceNineSixteenths (parameter : Gaussian) (box : Box) where
  leftNonzero :
    CCL.Riemann.SquareRootContinuationChain.Owner.verticalDeterminant
      parameter box.xLower ≠ 0
  rightNonzero :
    CCL.Riemann.SquareRootContinuationChain.Owner.verticalDeterminant
      parameter box.xUpper ≠ 0
  bottomNonzero :
    CCL.Riemann.SquareRootContinuationChain.Owner.horizontalDeterminant
      parameter box.yLower ≠ 0
  topNonzero :
    CCL.Riemann.SquareRootContinuationChain.Owner.horizontalDeterminant
      parameter box.yUpper ≠ 0
  directBound_le :
    min
      (CCL.Riemann.ExactQuadraticOwnerClearance.directVerticalClearanceBound
        parameter box box.xLower)
      (min
        (CCL.Riemann.ExactQuadraticOwnerClearance.directVerticalClearanceBound
          parameter box box.xUpper)
        (min
          (CCL.Riemann.ExactQuadraticOwnerClearance.directHorizontalClearanceBound
            parameter box box.yLower)
          (CCL.Riemann.ExactQuadraticOwnerClearance.directHorizontalClearanceBound
            parameter box box.yUpper))) ≤ (9 / 16 : Q)

theorem firstConnectorMiddleDirectCache :
    DirectClearanceNineSixteenths (firstConnectorGridParameter 4)
      firstConnectorBoxOne := by
  refine
    { leftNonzero := ?_
      rightNonzero := ?_
      bottomNonzero := ?_
      topNonzero := ?_
      directBound_le := ?_ }
  all_goals with_unfolding_all decide +revert

theorem firstConnectorOwnerFourAmbientLeftLeNineSixteenths :
    firstConnectorOwnerFour.track.initial.ambientLeftClearance.bound ≤
      (9 / 16 : Q) :=
  firstConnectorEdgeThreeStep.nextAmbientLeftLeNineSixteenths

theorem firstConnectorOwnerFourClearanceLeNineSixteenths :
    firstConnectorOwnerFour.track.initial.clearance.bound ≤ (9 / 16 : Q) :=
  firstConnectorEdgeThreeStep.advanceCache.dominance.left.trans
    firstConnectorOwnerFourAmbientLeftLeNineSixteenths

theorem firstConnectorOwnerFourNotCarries :
    ¬ CCL.Riemann.ClearSheetContinuation.variationBound firstConnectorSegment
        (firstConnectorEdgeRequest 3).endpoint.parameter
          (firstConnectorEdgeRequest 4).endpoint.parameter <
      firstConnectorOwnerFour.track.initial.clearance.bound := by
  apply not_lt_of_ge
  exact firstConnectorOwnerFourClearanceLeNineSixteenths.trans
    (nineSixteenthsLeThirtyNineSixtyFour.trans
      (firstConnectorMeshVariationBounds 4).1)

theorem firstConnectorOwnerFourStrengthenedClearanceLeNineSixteenths :
    (CCL.Riemann.ExactQuadraticOwnerClearance.strengthenQuadraticOwner
      firstConnectorOwnerFour).track.initial.clearance.bound ≤
        (9 / 16 : Q) := by
  let cache : DirectClearanceNineSixteenths
      (CCL.Riemann.FinitePeriodExamples.quarticCurve.polynomial.eval
        (firstConnectorSegment.pointAt
          (firstConnectorEdgeRequest 3).endpoint.parameter))
        firstConnectorOwnerFour.track.initial.box := by
    rw [firstConnectorOwnerFourBoxEq,
      quarticPolynomial_eval_firstConnectorEndpointFour]
    exact firstConnectorMiddleDirectCache
  rw [CCL.Riemann.ExactQuadraticOwnerClearance.strengthenQuadraticOwner_clearance_eq_max
    firstConnectorOwnerFour cache.leftNonzero cache.rightNonzero
      cache.bottomNonzero cache.topNonzero]
  apply max_le firstConnectorOwnerFourClearanceLeNineSixteenths
  rw [CCL.Riemann.ExactQuadraticOwnerClearance.directBoundaryClearance_bound]
  exact cache.directBound_le

theorem firstConnectorOwnerFourStrengthenedNotCarries :
    ¬ CCL.Riemann.ClearSheetContinuation.variationBound firstConnectorSegment
        (firstConnectorEdgeRequest 3).endpoint.parameter
          (firstConnectorEdgeRequest 4).endpoint.parameter <
      (CCL.Riemann.ExactQuadraticOwnerClearance.strengthenQuadraticOwner
        firstConnectorOwnerFour).track.initial.clearance.bound := by
  apply not_lt_of_ge
  exact firstConnectorOwnerFourStrengthenedClearanceLeNineSixteenths.trans
    (nineSixteenthsLeThirtyNineSixtyFour.trans
      (firstConnectorMeshVariationBounds 4).1)

/-! ## The midpoint moving reset -/

private theorem firstConnectorBoxOneProper : firstConnectorBoxOne.Proper := by
  constructor <;> with_unfolding_all decide

theorem firstConnectorMiddleBoxProjection :
    CCL.Riemann.ExactQuadraticOwnerClearance.movingRecenterBox?
        (CCL.Riemann.FinitePeriodExamples.quarticCurve.polynomial.eval
          (firstConnectorSegment.pointAt
            (firstConnectorEdgeRequest 3).endpoint.parameter))
        firstConnectorOwnerFour.parameterNonzero firstConnectorBoxOne
          firstConnectorBoxOneProper = some firstConnectorBoxTwo := by
  cases quarticPolynomial_eval_firstConnectorEndpointFour
  with_unfolding_all rfl

theorem firstConnectorOwnerFourReady :
    CCL.Riemann.PreparedSheetContinuation.AlreadyPrepared firstConnectorSegment
      (firstConnectorEdgeRequest 3).endpoint firstConnectorOwnerFour
        (firstConnectorEdgeRequest 4) := by
  refine ⟨?_, ?_, ?_⟩
  · rw [firstConnectorOwnerFourBoxEq]
    exact firstConnectorBoxOneSmall 4
  · exact
      (CCL.Riemann.UniformSquareRootPreparation.predictedClearance_le_transportFloor
        firstConnectorSegment (firstConnectorEdgeRequest 4).rootDiameter
          (firstConnectorEdgeRequest 4).rootDiameterPositive
            firstConnectorDerivativeMarginLe).trans
        firstConnectorEdgeThreeStep.advanceCache.clearanceFloor
  · rw [firstConnectorOwnerFourBoxEq]
    exact firstConnectorBoxOneRefines

def firstConnectorMiddleMovingCache :
    { reset : CCL.Riemann.ExactQuadraticOwnerClearance.MovingRecenter
        _ firstConnectorOwnerFour //
      CCL.Riemann.ExactQuadraticOwnerClearance.movingRecenter?
        firstConnectorOwnerFour = some reset } := by
  generalize found :
    CCL.Riemann.ExactQuadraticOwnerClearance.movingRecenter?
      firstConnectorOwnerFour = result
  cases result with
  | none =>
      have succeeds : Option.map
          (fun reset => reset.ownerBox)
          (CCL.Riemann.ExactQuadraticOwnerClearance.movingRecenter?
            firstConnectorOwnerFour) = some firstConnectorBoxTwo := by
        rw [CCL.Riemann.ExactQuadraticOwnerClearance.movingRecenter_ownerBox_map_of_box
          firstConnectorOwnerFour
              firstConnectorBoxOne firstConnectorBoxOneProper
                firstConnectorOwnerFourBoxEq,
          firstConnectorMiddleBoxProjection]
      rw [found] at succeeds
      contradiction
  | some reset => exact ⟨reset, rfl⟩

def firstConnectorMiddleMoving := firstConnectorMiddleMovingCache.1

theorem firstConnectorMiddleMovingFound :
    CCL.Riemann.ExactQuadraticOwnerClearance.movingRecenter?
      firstConnectorOwnerFour = some firstConnectorMiddleMoving :=
  firstConnectorMiddleMovingCache.2

theorem firstConnectorMiddleRecenteredEq :
    CCL.Riemann.PreparedSheetContinuation.recentered firstConnectorOwnerFour =
      firstConnectorMiddleMoving.owner :=
  CCL.Riemann.PreparedSheetContinuation.recentered_eq_of_movingRecenter_eq_some
    firstConnectorOwnerFour firstConnectorMiddleMoving
      firstConnectorMiddleMovingFound

theorem firstConnectorMiddleMovingBoxEq :
    firstConnectorMiddleMoving.ownerBox = firstConnectorBoxTwo := by
  have mapped : Option.map
      (fun reset => reset.ownerBox)
      (CCL.Riemann.ExactQuadraticOwnerClearance.movingRecenter?
        firstConnectorOwnerFour) = some firstConnectorBoxTwo := by
    rw [CCL.Riemann.ExactQuadraticOwnerClearance.movingRecenter_ownerBox_map_of_box
      firstConnectorOwnerFour
          firstConnectorBoxOne firstConnectorBoxOneProper
            firstConnectorOwnerFourBoxEq,
      firstConnectorMiddleBoxProjection]
  rw [firstConnectorMiddleMovingFound] at mapped
  exact Option.some.inj mapped

theorem firstConnectorMiddleMovingClearance : (1 : Q) ≤
    firstConnectorMiddleMoving.owner.track.initial.clearance.bound := by
  rw [firstConnectorMiddleMoving.ownerDirectClearanceBound]
  apply CCL.Riemann.ExactQuadraticOwnerClearance.le_directBoundaryClearance_bound
  all_goals rw [firstConnectorMiddleMovingBoxEq]
  all_goals change (1 : Q) ≤ _
  all_goals rw [quarticPolynomial_eval_firstConnectorEndpointFour]
  all_goals with_unfolding_all decide

private theorem firstConnectorBoxTwoSmall (edge : Fin 8) :
    firstConnectorBoxTwo.diagonalSq <
      (firstConnectorEdgeRequest edge).rootDiameter := by
  change firstConnectorBoxTwo.diagonalSq < workingRootDiameter
  with_unfolding_all decide

private theorem firstConnectorBoxTwoRefines :
    firstConnectorBoxTwo.Refines
      (CCL.Riemann.UniformSquareRootPreparation.rootAmbient
        firstConnectorSegment) := by
  change
    -CCL.Riemann.UniformSquareRootPreparation.rootAmbientRadius
        firstConnectorSegment ≤ firstConnectorBoxTwo.xLower ∧
      firstConnectorBoxTwo.xUpper ≤
        CCL.Riemann.UniformSquareRootPreparation.rootAmbientRadius
          firstConnectorSegment ∧
      -CCL.Riemann.UniformSquareRootPreparation.rootAmbientRadius
        firstConnectorSegment ≤ firstConnectorBoxTwo.yLower ∧
      firstConnectorBoxTwo.yUpper ≤
        CCL.Riemann.UniformSquareRootPreparation.rootAmbientRadius
          firstConnectorSegment
  have threeLe :=
    CCL.Riemann.UniformSquareRootPreparation.three_le_rootAmbientRadius
      firstConnectorSegment
  exact ⟨(RFAP.ConstructiveFraction.neg_le_neg_direct threeLe).trans
      (by with_unfolding_all decide),
    (by with_unfolding_all decide :
      firstConnectorBoxTwo.xUpper ≤ (3 : Q)).trans threeLe,
    (RFAP.ConstructiveFraction.neg_le_neg_direct threeLe).trans
      (by with_unfolding_all decide),
    (by with_unfolding_all decide :
      firstConnectorBoxTwo.yUpper ≤ (3 : Q)).trans threeLe⟩

theorem firstConnectorMiddleRecenteredReady :
    CCL.Riemann.PreparedSheetContinuation.AlreadyPrepared firstConnectorSegment
      (firstConnectorEdgeRequest 3).endpoint
        (CCL.Riemann.PreparedSheetContinuation.recentered
          firstConnectorOwnerFour) (firstConnectorEdgeRequest 4) := by
  rw [firstConnectorMiddleRecenteredEq]
  refine ⟨?_, ?_, ?_⟩
  · rw [firstConnectorMiddleMoving.ownerInitialBox,
      firstConnectorMiddleMovingBoxEq]
    exact firstConnectorBoxTwoSmall 4
  · exact
      (CCL.Riemann.UniformSquareRootPreparation.predictedClearance_le_oneOver128
        firstConnectorSegment (firstConnectorEdgeRequest 4).rootDiameter
          (firstConnectorEdgeRequest 4).rootDiameterPositive
            firstConnectorDerivativeMarginLe).trans
        (oneOver128LeOne.trans firstConnectorMiddleMovingClearance)
  · rw [firstConnectorMiddleMoving.ownerInitialBox,
      firstConnectorMiddleMovingBoxEq]
    exact firstConnectorBoxTwoRefines

theorem firstConnectorMiddleRecenteredCarries :
    CCL.Riemann.ClearSheetContinuation.variationBound firstConnectorSegment
        (firstConnectorEdgeRequest 3).endpoint.parameter
          (firstConnectorEdgeRequest 4).endpoint.parameter <
      (CCL.Riemann.PreparedSheetContinuation.recentered
        firstConnectorOwnerFour).track.initial.clearance.bound := by
  rw [firstConnectorMiddleRecenteredEq]
  exact ((firstConnectorMeshVariationBounds 4).2.trans_eq
    fortyOver64EqFiveEighths).trans_le
      ((show (5 / 8 : Q) ≤ 1 by with_unfolding_all decide).trans
        firstConnectorMiddleMovingClearance)

theorem firstConnectorMiddlePreparedEqRecentered :
    CCL.Riemann.PreparedSheetContinuation.prepared firstConnectorSegment
        (firstConnectorEdgeRequest 3).endpoint firstConnectorOwnerFour
          (firstConnectorEdgeRequest 4) =
      CCL.Riemann.PreparedSheetContinuation.recentered
        firstConnectorOwnerFour :=
  CCL.Riemann.PreparedSheetContinuation.prepared_eq_recentered_of_ready
    firstConnectorSegment (firstConnectorEdgeRequest 3).endpoint
      firstConnectorOwnerFour (firstConnectorEdgeRequest 4)
        firstConnectorOwnerFourReady firstConnectorOwnerFourNotCarries
          firstConnectorOwnerFourStrengthenedNotCarries
            firstConnectorMiddleRecenteredReady
              firstConnectorMiddleRecenteredCarries

theorem firstConnectorMiddleCanonicalSmall :
    CCL.Riemann.ClearSheetContinuation.variationBound firstConnectorSegment
        (firstConnectorEdgeRequest 3).endpoint.parameter
          (firstConnectorEdgeRequest 4).endpoint.parameter <
      (CCL.Riemann.PreparedSheetContinuation.prepared firstConnectorSegment
        (firstConnectorEdgeRequest 3).endpoint firstConnectorOwnerFour
          (firstConnectorEdgeRequest 4)).track.initial.clearance.bound :=
  CCL.Riemann.PreparedSheetContinuation.variation_lt_prepared_of_ready_of_recenteredCarries
    firstConnectorSegment (firstConnectorEdgeRequest 3).endpoint
      firstConnectorOwnerFour (firstConnectorEdgeRequest 4)
        firstConnectorOwnerFourReady firstConnectorMiddleRecenteredReady
          firstConnectorMiddleRecenteredCarries

def firstConnectorMiddleCachedSource :=
  CCL.Riemann.PreparedSheetContinuation.CachedSource.canonical
    firstConnectorSegment (firstConnectorEdgeRequest 3).endpoint
      firstConnectorOwnerFour (firstConnectorEdgeRequest 4)

private theorem quarterSquare_le_threeHalves_of_le_two
    (bound : Q) (nonnegative : 0 ≤ bound) (upper : bound ≤ 2) :
    bound ^ 2 / 4 ≤ (3 / 2 : Q) := by
  have squareLe : bound ^ 2 ≤ (2 : Q) ^ 2 :=
    RFAP.ConstructiveFraction.pow_le_pow_direct nonnegative upper 2
  calc
    bound ^ 2 / 4 ≤ (2 : Q) ^ 2 / 4 := by
      change bound ^ 2 * (4 : Q)⁻¹ ≤ (2 : Q) ^ 2 * (4 : Q)⁻¹
      exact RFAP.ConstructiveFraction.mul_le_mul_of_nonneg_right_direct
        squareLe (RFAP.ConstructiveFraction.inv_pos_direct (by decide)).le
    _ ≤ (3 / 2 : Q) := by with_unfolding_all decide

theorem firstConnectorMiddleRecenteredAmbientLeftLeTwo :
    (CCL.Riemann.PreparedSheetContinuation.recentered
      firstConnectorOwnerFour).track.initial.ambientLeftClearance.bound ≤
        (2 : Q) := by
  rw [firstConnectorMiddleRecenteredEq,
    firstConnectorMiddleMoving.ownerAmbientLeftClearanceBound,
    CCL.Riemann.ExactQuadraticOwnerClearance.directBoundaryClearance_bound,
    firstConnectorMiddleMovingBoxEq,
    quarticPolynomial_eval_firstConnectorEndpointFour]
  with_unfolding_all decide

theorem firstConnectorMiddlePreparedAmbientLeftLeTwo :
    firstConnectorMiddleCachedSource.preparedOwner.track.initial.ambientLeftClearance.bound ≤
      (2 : Q) := by
  rw [show firstConnectorMiddleCachedSource.preparedOwner =
      CCL.Riemann.PreparedSheetContinuation.prepared firstConnectorSegment
        (firstConnectorEdgeRequest 3).endpoint firstConnectorOwnerFour
          (firstConnectorEdgeRequest 4) by rfl,
    firstConnectorMiddlePreparedEqRecentered]
  exact firstConnectorMiddleRecenteredAmbientLeftLeTwo

theorem firstConnectorMiddleRecenteredBudget :
    CCL.Riemann.ExactQuadraticOwnerClearance.QuadraticAmbientBudget
      (CCL.Riemann.PreparedSheetContinuation.recentered
        firstConnectorOwnerFour) := by
  rw [firstConnectorMiddleRecenteredEq]
  apply CCL.Riemann.ExactQuadraticOwnerClearance.quadraticAmbientBudget_of_box
    firstConnectorMiddleMoving.owner firstConnectorBoxTwo
  · exact firstConnectorMiddleMoving.ownerInitialBox.trans
      firstConnectorMiddleMovingBoxEq
  · exact firstConnectorMiddleMoving.ownerAmbientBox.trans
      firstConnectorMiddleMovingBoxEq
  · rw [quarticPolynomial_eval_firstConnectorEndpointFour]
    exact firstConnectorGridParameterNormSqLe 4
  all_goals with_unfolding_all decide

theorem firstConnectorMiddlePreparedDominance :
    CCL.Riemann.ExactQuadraticOwnerClearance.AmbientClearanceDominance
      firstConnectorMiddleCachedSource.preparedOwner :=
  CCL.Riemann.PreparedSheetContinuation.prepared_ambientClearanceDominance_of_ready_of_recenteredCarries
    firstConnectorSegment (firstConnectorEdgeRequest 3).endpoint
      firstConnectorOwnerFour (firstConnectorEdgeRequest 4)
        firstConnectorOwnerFourReady firstConnectorMiddleRecenteredReady
          firstConnectorMiddleRecenteredCarries
            firstConnectorEdgeThreeStep.advanceCache.dominance

theorem firstConnectorMiddlePreparedBudget :
    CCL.Riemann.ExactQuadraticOwnerClearance.QuadraticAmbientBudget
      firstConnectorMiddleCachedSource.preparedOwner :=
  CCL.Riemann.PreparedSheetContinuation.prepared_quadraticAmbientBudget_of_ready_of_recenteredCarries
    firstConnectorSegment (firstConnectorEdgeRequest 3).endpoint
      firstConnectorOwnerFour (firstConnectorEdgeRequest 4)
        firstConnectorOwnerFourReady firstConnectorMiddleRecenteredReady
          firstConnectorMiddleRecenteredCarries
            firstConnectorEdgeThreeStep.advanceCache.budget
              firstConnectorMiddleRecenteredBudget

theorem firstConnectorMiddleRecenteredMargin : (1 / 2 : Q) ≤
    (CCL.Riemann.PreparedSheetContinuation.recentered
        firstConnectorOwnerFour).track.initial.clearance.bound -
      RFAP.ConstructiveGaussian.Gaussian.normSq
        (CCL.Riemann.FinitePeriodExamples.quarticCurve.polynomial.eval
            (firstConnectorSegment.pointAt
              (firstConnectorEdgeRequest 3).endpoint.parameter) -
          CCL.Riemann.FinitePeriodExamples.quarticCurve.polynomial.eval
            (firstConnectorSegment.pointAt
              (firstConnectorEdgeRequest 4).endpoint.parameter)) :=
  (firstConnectorMeshVariationMargin 4).trans
    (RFAP.ConstructiveFraction.sub_le_sub_right_direct
      firstConnectorMiddleRecenteredCarries.le _)

theorem firstConnectorMiddlePreparedMargin : (1 / 2 : Q) ≤
    firstConnectorMiddleCachedSource.preparedOwner.track.initial.clearance.bound -
      RFAP.ConstructiveGaussian.Gaussian.normSq
        (CCL.Riemann.FinitePeriodExamples.quarticCurve.polynomial.eval
            (firstConnectorSegment.pointAt
              (firstConnectorEdgeRequest 3).endpoint.parameter) -
          CCL.Riemann.FinitePeriodExamples.quarticCurve.polynomial.eval
            (firstConnectorSegment.pointAt
              (firstConnectorEdgeRequest 4).endpoint.parameter)) :=
  CCL.Riemann.PreparedSheetContinuation.prepared_margin_lower_of_ready_of_recenteredCarries
    firstConnectorSegment (firstConnectorEdgeRequest 3).endpoint
      firstConnectorOwnerFour (firstConnectorEdgeRequest 4)
        firstConnectorOwnerFourReady firstConnectorMiddleRecenteredReady
          firstConnectorMiddleRecenteredCarries (1 / 2) _
            (firstConnectorMeshVariationMargin 4)
              firstConnectorMiddleRecenteredMargin

theorem firstConnectorEdgeFourAdvanceCache :
    CCL.Riemann.PreparedSheetContinuation.QuadraticAdvanceCache
      firstConnectorSegment firstConnectorSegment_withinAmbient
        (firstConnectorEdgeRequest 3).endpoint firstConnectorOwnerFour
          (firstConnectorEdgeRequest 4) firstConnectorMiddleCachedSource
            firstConnectorMiddleCanonicalSmall := by
  apply CCL.Riemann.PreparedSheetContinuation.quadraticAdvanceCache
  · rw [quarticPolynomial_eval_firstConnectorEndpointFour,
      show
      CCL.Riemann.FinitePeriodExamples.quarticCurve.polynomial.eval
          (firstConnectorSegment.pointAt
            (firstConnectorEdgeRequest 4).endpoint.parameter) =
        firstConnectorGridParameter 5 by
          exact quarticPolynomial_eval_firstConnectorMeshEndpoint 5]
    exact firstConnectorAdjacentParametersDifferent 4
  · exact firstConnectorDerivativeMarginLe
  · exact firstConnectorMiddlePreparedDominance
  · exact firstConnectorMiddlePreparedMargin
  · exact firstConnectorMiddlePreparedBudget
  · rw [show
      CCL.Riemann.FinitePeriodExamples.quarticCurve.polynomial.eval
          (firstConnectorSegment.pointAt
            (firstConnectorEdgeRequest 4).endpoint.parameter) =
        firstConnectorGridParameter 5 by
          exact quarticPolynomial_eval_firstConnectorMeshEndpoint 5]
    exact firstConnectorGridParameterNormSqLe 5

/-! ## Same-box completion of the second half -/

def firstConnectorOwnerFive :=
  CCL.Riemann.PreparedSheetContinuation.advanceCached firstConnectorSegment
    firstConnectorSegment_withinAmbient (firstConnectorEdgeRequest 3).endpoint
      firstConnectorOwnerFour (firstConnectorEdgeRequest 4)
        firstConnectorMiddleCachedSource firstConnectorMiddleCanonicalSmall

theorem firstConnectorOwnerFiveBoxEq :
    firstConnectorOwnerFive.track.initial.box = firstConnectorBoxTwo := by
  calc
    firstConnectorOwnerFive.track.initial.box =
        firstConnectorMiddleCachedSource.preparedOwner.track.initial.box :=
      firstConnectorEdgeFourAdvanceCache.initialBox
    _ = (CCL.Riemann.PreparedSheetContinuation.recentered
        firstConnectorOwnerFour).track.initial.box := by
      rw [show firstConnectorMiddleCachedSource.preparedOwner =
          CCL.Riemann.PreparedSheetContinuation.prepared firstConnectorSegment
            (firstConnectorEdgeRequest 3).endpoint firstConnectorOwnerFour
              (firstConnectorEdgeRequest 4) by rfl,
        firstConnectorMiddlePreparedEqRecentered]
    _ = firstConnectorBoxTwo := by
      rw [firstConnectorMiddleRecenteredEq,
        firstConnectorMiddleMoving.ownerInitialBox,
          firstConnectorMiddleMovingBoxEq]

theorem firstConnectorOwnerFiveAmbientLeftLeThreeHalves :
    firstConnectorOwnerFive.track.initial.ambientLeftClearance.bound ≤
      (3 / 2 : Q) :=
  firstConnectorEdgeFourAdvanceCache.ambientLeftQuarterSq.trans
    (quarterSquare_le_threeHalves_of_le_two _
      firstConnectorMiddleCachedSource.preparedOwner.track.initial.ambientLeftClearance.positive.le
      firstConnectorMiddlePreparedAmbientLeftLeTwo)

theorem firstConnectorEdgeFiveStep : SameBoxStep 5 firstConnectorOwnerFive :=
  sameBoxStep 5 firstConnectorOwnerFive firstConnectorBoxTwo
    firstConnectorOwnerFiveBoxEq (firstConnectorBoxTwoSmall 5)
      firstConnectorBoxTwoRefines firstConnectorEdgeFourAdvanceCache.clearanceFloor
        firstConnectorEdgeFourAdvanceCache.dominance
          firstConnectorEdgeFourAdvanceCache.budget
            firstConnectorOwnerFiveAmbientLeftLeThreeHalves
              (firstConnectorBoxTwoClearance 0)

def firstConnectorOwnerSix := firstConnectorEdgeFiveStep.nextOwner

theorem firstConnectorOwnerSixBoxEq :
    firstConnectorOwnerSix.track.initial.box = firstConnectorBoxTwo :=
  firstConnectorEdgeFiveStep.nextOwnerBoxEq firstConnectorBoxTwo
    firstConnectorOwnerFiveBoxEq

theorem firstConnectorEdgeSixStep : SameBoxStep 6 firstConnectorOwnerSix :=
  sameBoxStep 6 firstConnectorOwnerSix firstConnectorBoxTwo
    firstConnectorOwnerSixBoxEq (firstConnectorBoxTwoSmall 6)
      firstConnectorBoxTwoRefines
        firstConnectorEdgeFiveStep.advanceCache.clearanceFloor
          firstConnectorEdgeFiveStep.advanceCache.dominance
            firstConnectorEdgeFiveStep.advanceCache.budget
              (firstConnectorEdgeFiveStep.nextAmbientLeftLeNineSixteenths.trans
                (by decide)) (firstConnectorBoxTwoClearance 1)

def firstConnectorOwnerSeven := firstConnectorEdgeSixStep.nextOwner

theorem firstConnectorOwnerSevenBoxEq :
    firstConnectorOwnerSeven.track.initial.box = firstConnectorBoxTwo :=
  firstConnectorEdgeSixStep.nextOwnerBoxEq firstConnectorBoxTwo
    firstConnectorOwnerSixBoxEq

theorem firstConnectorEdgeSevenStep : SameBoxStep 7 firstConnectorOwnerSeven :=
  sameBoxStep 7 firstConnectorOwnerSeven firstConnectorBoxTwo
    firstConnectorOwnerSevenBoxEq (firstConnectorBoxTwoSmall 7)
      firstConnectorBoxTwoRefines
        firstConnectorEdgeSixStep.advanceCache.clearanceFloor
          firstConnectorEdgeSixStep.advanceCache.dominance
            firstConnectorEdgeSixStep.advanceCache.budget
              (firstConnectorEdgeSixStep.nextAmbientLeftLeNineSixteenths.trans
                (by decide)) (firstConnectorBoxTwoClearance 2)

def firstConnectorOwnerEight := firstConnectorEdgeSevenStep.nextOwner

theorem firstConnectorOwnerEightBoxEq :
    firstConnectorOwnerEight.track.initial.box = firstConnectorBoxTwo :=
  firstConnectorEdgeSevenStep.nextOwnerBoxEq firstConnectorBoxTwo
    firstConnectorOwnerSevenBoxEq

/-! ## The complete cached depth-three subdivision -/

theorem firstConnectorEdgeOrdered (edge : Fin 8) :
    (firstConnectorMeshEndpoint
        (firstConnectorEdgeSource edge)).parameter ≤
      (firstConnectorEdgeRequest edge).endpoint.parameter := by
  rcases finEightCases edge with h | h | h | h | h | h | h | h
  all_goals subst edge
  all_goals with_unfolding_all decide

/-- The retained parameter edge corresponding to one cached mesh request. -/
def firstConnectorParameterEdge (edge : Fin 8) :
    CCL.Riemann.ClearSheetContinuation.Subdivision.ParameterEdge :=
  ⟨firstConnectorMeshEndpoint (firstConnectorEdgeSource edge),
    (firstConnectorEdgeRequest edge).endpoint⟩

def firstConnectorTailEight :
    CCL.Riemann.PreparedSheetContinuation.Subdivision firstConnectorSegment
      firstConnectorSegment_withinAmbient (firstConnectorMeshEndpoint 8)
        firstConnectorOwnerEight :=
  .stop (firstConnectorMeshEndpoint 8) firstConnectorOwnerEight

def firstConnectorTailSeven :
    CCL.Riemann.PreparedSheetContinuation.Subdivision firstConnectorSegment
      firstConnectorSegment_withinAmbient (firstConnectorMeshEndpoint 7)
        firstConnectorOwnerSeven :=
  CCL.Riemann.PreparedSheetContinuation.Subdivision.nextCached
    firstConnectorSegment firstConnectorSegment_withinAmbient
      (firstConnectorMeshEndpoint 7) firstConnectorOwnerSeven
        (firstConnectorEdgeRequest 7)
          (CCL.Riemann.PreparedSheetContinuation.CachedSource.canonical
            firstConnectorSegment (firstConnectorMeshEndpoint 7)
              firstConnectorOwnerSeven (firstConnectorEdgeRequest 7))
          (firstConnectorEdgeOrdered 7)
          firstConnectorEdgeSevenStep.canonicalSmall
          firstConnectorEdgeSevenStep.canonicalSmall firstConnectorTailEight

def firstConnectorTailSix :
    CCL.Riemann.PreparedSheetContinuation.Subdivision firstConnectorSegment
      firstConnectorSegment_withinAmbient (firstConnectorMeshEndpoint 6)
        firstConnectorOwnerSix :=
  CCL.Riemann.PreparedSheetContinuation.Subdivision.nextCached
    firstConnectorSegment firstConnectorSegment_withinAmbient
      (firstConnectorMeshEndpoint 6) firstConnectorOwnerSix
        (firstConnectorEdgeRequest 6)
          (CCL.Riemann.PreparedSheetContinuation.CachedSource.canonical
            firstConnectorSegment (firstConnectorMeshEndpoint 6)
              firstConnectorOwnerSix (firstConnectorEdgeRequest 6))
          (firstConnectorEdgeOrdered 6)
          firstConnectorEdgeSixStep.canonicalSmall
          firstConnectorEdgeSixStep.canonicalSmall firstConnectorTailSeven

def firstConnectorTailFive :
    CCL.Riemann.PreparedSheetContinuation.Subdivision firstConnectorSegment
      firstConnectorSegment_withinAmbient (firstConnectorMeshEndpoint 5)
        firstConnectorOwnerFive :=
  CCL.Riemann.PreparedSheetContinuation.Subdivision.nextCached
    firstConnectorSegment firstConnectorSegment_withinAmbient
      (firstConnectorMeshEndpoint 5) firstConnectorOwnerFive
        (firstConnectorEdgeRequest 5)
          (CCL.Riemann.PreparedSheetContinuation.CachedSource.canonical
            firstConnectorSegment (firstConnectorMeshEndpoint 5)
              firstConnectorOwnerFive (firstConnectorEdgeRequest 5))
          (firstConnectorEdgeOrdered 5)
          firstConnectorEdgeFiveStep.canonicalSmall
          firstConnectorEdgeFiveStep.canonicalSmall firstConnectorTailSix

def firstConnectorTailFour :
    CCL.Riemann.PreparedSheetContinuation.Subdivision firstConnectorSegment
      firstConnectorSegment_withinAmbient (firstConnectorMeshEndpoint 4)
        firstConnectorOwnerFour :=
  CCL.Riemann.PreparedSheetContinuation.Subdivision.nextCached
    firstConnectorSegment firstConnectorSegment_withinAmbient
      (firstConnectorMeshEndpoint 4) firstConnectorOwnerFour
        (firstConnectorEdgeRequest 4) firstConnectorMiddleCachedSource
          (firstConnectorEdgeOrdered 4) firstConnectorMiddleCanonicalSmall
            firstConnectorMiddleCanonicalSmall firstConnectorTailFive

def firstConnectorTailThree :
    CCL.Riemann.PreparedSheetContinuation.Subdivision firstConnectorSegment
      firstConnectorSegment_withinAmbient (firstConnectorMeshEndpoint 3)
        firstConnectorOwnerThree :=
  CCL.Riemann.PreparedSheetContinuation.Subdivision.nextCached
    firstConnectorSegment firstConnectorSegment_withinAmbient
      (firstConnectorMeshEndpoint 3) firstConnectorOwnerThree
        (firstConnectorEdgeRequest 3)
          (CCL.Riemann.PreparedSheetContinuation.CachedSource.canonical
            firstConnectorSegment (firstConnectorMeshEndpoint 3)
              firstConnectorOwnerThree (firstConnectorEdgeRequest 3))
          (firstConnectorEdgeOrdered 3)
          firstConnectorEdgeThreeStep.canonicalSmall
          firstConnectorEdgeThreeStep.canonicalSmall firstConnectorTailFour

def firstConnectorTailTwo :
    CCL.Riemann.PreparedSheetContinuation.Subdivision firstConnectorSegment
      firstConnectorSegment_withinAmbient (firstConnectorMeshEndpoint 2)
        firstConnectorOwnerTwo :=
  CCL.Riemann.PreparedSheetContinuation.Subdivision.nextCached
    firstConnectorSegment firstConnectorSegment_withinAmbient
      (firstConnectorMeshEndpoint 2) firstConnectorOwnerTwo
        (firstConnectorEdgeRequest 2)
          (CCL.Riemann.PreparedSheetContinuation.CachedSource.canonical
            firstConnectorSegment (firstConnectorMeshEndpoint 2)
              firstConnectorOwnerTwo (firstConnectorEdgeRequest 2))
          (firstConnectorEdgeOrdered 2)
          firstConnectorEdgeTwoStep.canonicalSmall
          firstConnectorEdgeTwoStep.canonicalSmall firstConnectorTailThree

def firstConnectorTailOne :
    CCL.Riemann.PreparedSheetContinuation.Subdivision firstConnectorSegment
      firstConnectorSegment_withinAmbient (firstConnectorMeshEndpoint 1)
        firstConnectorOwnerOne :=
  CCL.Riemann.PreparedSheetContinuation.Subdivision.nextCached
    firstConnectorSegment firstConnectorSegment_withinAmbient
      (firstConnectorMeshEndpoint 1) firstConnectorOwnerOne
        (firstConnectorEdgeRequest 1) firstConnectorOwnerOneCachedSource
          (firstConnectorEdgeOrdered 1) firstConnectorOwnerOneCanonicalSmall
            firstConnectorOwnerOneCanonicalSmall firstConnectorTailTwo

def firstConnectorSubdivision :
    CCL.Riemann.PreparedSheetContinuation.Subdivision firstConnectorSegment
      firstConnectorSegment_withinAmbient
        CCL.Riemann.PreparedClearPathModels.zeroEndpoint
          firstConnectorStartOwner :=
  CCL.Riemann.PreparedSheetContinuation.Subdivision.nextCached
    firstConnectorSegment firstConnectorSegment_withinAmbient
      CCL.Riemann.PreparedClearPathModels.zeroEndpoint firstConnectorStartOwner
        (firstConnectorEdgeRequest 0) firstConnectorCachedSource
          (firstConnectorEdgeOrdered 0) firstConnectorCanonicalSmall
            firstConnectorCanonicalSmall firstConnectorTailOne

def firstConnectorInputOwner :=
  CCL.Riemann.PreparedClearPathModels.ownerAtStart
    firstRawConnectorHeadData.head (branchSquareRootOwner 0 0)

def firstConnectorCompleteSegment :
    CCL.Riemann.PreparedClearPathModels.CompleteSegment firstConnectorSegment
      firstConnectorSegment_withinAmbient firstConnectorInputOwner where
  subdivision := firstConnectorSubdivision
  endpoint_eq := by
    simp only [firstConnectorSubdivision, firstConnectorTailOne,
      firstConnectorTailTwo, firstConnectorTailThree, firstConnectorTailFour,
      firstConnectorTailFive, firstConnectorTailSix, firstConnectorTailSeven,
      firstConnectorTailEight]
    rfl

theorem firstConnectorTailEightParameterEdges :
    firstConnectorTailEight.parameterEdges = [] := rfl

theorem firstConnectorTailSevenParameterEdges :
    firstConnectorTailSeven.parameterEdges =
      firstConnectorParameterEdge 7 :: [] := by
  simp only [firstConnectorTailSeven,
    CCL.Riemann.PreparedSheetContinuation.Subdivision.nextCached_parameterEdges,
    firstConnectorParameterEdge, firstConnectorEdgeSource]
  rfl

theorem firstConnectorTailSixParameterEdges :
    firstConnectorTailSix.parameterEdges =
      firstConnectorParameterEdge 6 ::
        firstConnectorTailSeven.parameterEdges := by
  simp only [firstConnectorTailSix,
    CCL.Riemann.PreparedSheetContinuation.Subdivision.nextCached_parameterEdges,
    firstConnectorParameterEdge, firstConnectorEdgeSource]
  rfl

theorem firstConnectorTailFiveParameterEdges :
    firstConnectorTailFive.parameterEdges =
      firstConnectorParameterEdge 5 ::
        firstConnectorTailSix.parameterEdges := by
  simp only [firstConnectorTailFive,
    CCL.Riemann.PreparedSheetContinuation.Subdivision.nextCached_parameterEdges,
    firstConnectorParameterEdge, firstConnectorEdgeSource]
  rfl

theorem firstConnectorTailFourParameterEdges :
    firstConnectorTailFour.parameterEdges =
      firstConnectorParameterEdge 4 ::
        firstConnectorTailFive.parameterEdges := by
  simp only [firstConnectorTailFour,
    CCL.Riemann.PreparedSheetContinuation.Subdivision.nextCached_parameterEdges,
    firstConnectorParameterEdge, firstConnectorEdgeSource]
  rfl

theorem firstConnectorTailThreeParameterEdges :
    firstConnectorTailThree.parameterEdges =
      firstConnectorParameterEdge 3 ::
        firstConnectorTailFour.parameterEdges := by
  simp only [firstConnectorTailThree,
    CCL.Riemann.PreparedSheetContinuation.Subdivision.nextCached_parameterEdges,
    firstConnectorParameterEdge, firstConnectorEdgeSource]
  rfl

theorem firstConnectorTailTwoParameterEdges :
    firstConnectorTailTwo.parameterEdges =
      firstConnectorParameterEdge 2 ::
        firstConnectorTailThree.parameterEdges := by
  simp only [firstConnectorTailTwo,
    CCL.Riemann.PreparedSheetContinuation.Subdivision.nextCached_parameterEdges,
    firstConnectorParameterEdge, firstConnectorEdgeSource]
  rfl

theorem firstConnectorTailOneParameterEdges :
    firstConnectorTailOne.parameterEdges =
      firstConnectorParameterEdge 1 ::
        firstConnectorTailTwo.parameterEdges := by
  simp only [firstConnectorTailOne,
    CCL.Riemann.PreparedSheetContinuation.Subdivision.nextCached_parameterEdges,
    firstConnectorParameterEdge, firstConnectorEdgeSource]
  rfl

theorem firstConnectorSubdivisionParameterEdges :
    firstConnectorSubdivision.parameterEdges =
      CCL.Riemann.ClearSheetContinuation.Subdivision.dyadicEdges 3
        CCL.Riemann.PreparedClearPathModels.zeroEndpoint
          CCL.Riemann.PreparedClearPathModels.oneEndpoint := by
  calc
    firstConnectorSubdivision.parameterEdges =
        firstConnectorParameterEdge 0 ::
          firstConnectorTailOne.parameterEdges := by
      simp only [firstConnectorSubdivision,
        CCL.Riemann.PreparedSheetContinuation.Subdivision.nextCached_parameterEdges,
        firstConnectorParameterEdge, firstConnectorEdgeSource]
      rfl
    _ = firstConnectorParameterEdge 0 :: firstConnectorParameterEdge 1 ::
        firstConnectorTailTwo.parameterEdges :=
      congrArg (List.cons (firstConnectorParameterEdge 0))
        firstConnectorTailOneParameterEdges
    _ = firstConnectorParameterEdge 0 :: firstConnectorParameterEdge 1 ::
        firstConnectorParameterEdge 2 ::
          firstConnectorTailThree.parameterEdges :=
      congrArg (List.cons (firstConnectorParameterEdge 0))
        (congrArg (List.cons (firstConnectorParameterEdge 1))
          firstConnectorTailTwoParameterEdges)
    _ = firstConnectorParameterEdge 0 :: firstConnectorParameterEdge 1 ::
        firstConnectorParameterEdge 2 :: firstConnectorParameterEdge 3 ::
          firstConnectorTailFour.parameterEdges :=
      congrArg (List.cons (firstConnectorParameterEdge 0))
        (congrArg (List.cons (firstConnectorParameterEdge 1))
          (congrArg (List.cons (firstConnectorParameterEdge 2))
            firstConnectorTailThreeParameterEdges))
    _ = firstConnectorParameterEdge 0 :: firstConnectorParameterEdge 1 ::
        firstConnectorParameterEdge 2 :: firstConnectorParameterEdge 3 ::
          firstConnectorParameterEdge 4 ::
            firstConnectorTailFive.parameterEdges :=
      congrArg (List.cons (firstConnectorParameterEdge 0))
        (congrArg (List.cons (firstConnectorParameterEdge 1))
          (congrArg (List.cons (firstConnectorParameterEdge 2))
            (congrArg (List.cons (firstConnectorParameterEdge 3))
              firstConnectorTailFourParameterEdges)))
    _ = firstConnectorParameterEdge 0 :: firstConnectorParameterEdge 1 ::
        firstConnectorParameterEdge 2 :: firstConnectorParameterEdge 3 ::
          firstConnectorParameterEdge 4 :: firstConnectorParameterEdge 5 ::
            firstConnectorTailSix.parameterEdges :=
      congrArg (List.cons (firstConnectorParameterEdge 0))
        (congrArg (List.cons (firstConnectorParameterEdge 1))
          (congrArg (List.cons (firstConnectorParameterEdge 2))
            (congrArg (List.cons (firstConnectorParameterEdge 3))
              (congrArg (List.cons (firstConnectorParameterEdge 4))
                firstConnectorTailFiveParameterEdges))))
    _ = firstConnectorParameterEdge 0 :: firstConnectorParameterEdge 1 ::
        firstConnectorParameterEdge 2 :: firstConnectorParameterEdge 3 ::
          firstConnectorParameterEdge 4 :: firstConnectorParameterEdge 5 ::
            firstConnectorParameterEdge 6 ::
              firstConnectorTailSeven.parameterEdges :=
      congrArg (List.cons (firstConnectorParameterEdge 0))
        (congrArg (List.cons (firstConnectorParameterEdge 1))
          (congrArg (List.cons (firstConnectorParameterEdge 2))
            (congrArg (List.cons (firstConnectorParameterEdge 3))
              (congrArg (List.cons (firstConnectorParameterEdge 4))
                (congrArg (List.cons (firstConnectorParameterEdge 5))
                  firstConnectorTailSixParameterEdges)))))
    _ = firstConnectorParameterEdge 0 :: firstConnectorParameterEdge 1 ::
        firstConnectorParameterEdge 2 :: firstConnectorParameterEdge 3 ::
          firstConnectorParameterEdge 4 :: firstConnectorParameterEdge 5 ::
            firstConnectorParameterEdge 6 :: firstConnectorParameterEdge 7 ::
              [] :=
      congrArg (List.cons (firstConnectorParameterEdge 0))
        (congrArg (List.cons (firstConnectorParameterEdge 1))
          (congrArg (List.cons (firstConnectorParameterEdge 2))
            (congrArg (List.cons (firstConnectorParameterEdge 3))
              (congrArg (List.cons (firstConnectorParameterEdge 4))
                (congrArg (List.cons (firstConnectorParameterEdge 5))
                  (congrArg (List.cons (firstConnectorParameterEdge 6))
                    firstConnectorTailSevenParameterEdges))))))
    _ = CCL.Riemann.ClearSheetContinuation.Subdivision.dyadicEdges 3
        CCL.Riemann.PreparedClearPathModels.zeroEndpoint
          CCL.Riemann.PreparedClearPathModels.oneEndpoint := by
      with_unfolding_all rfl

theorem firstConnectorSubdivisionStrictParameterEdges :
    CCL.Riemann.PreparedClearPathModels.PreparedPath.StrictParameterEdges
      firstConnectorSubdivision.parameterEdges := by
  rw [firstConnectorSubdivisionParameterEdges]
  exact CCL.Riemann.PreparedClearPathModels.PreparedPath.dyadicEdges_strictParameterEdges 3
      CCL.Riemann.PreparedClearPathModels.zeroEndpoint
        CCL.Riemann.PreparedClearPathModels.oneEndpoint (by decide)

theorem firstConnectorSubdivisionStepCount :
    firstConnectorSubdivision.stepCount = 2 ^ 3 := by
  calc
    firstConnectorSubdivision.stepCount =
        firstConnectorSubdivision.parameterEdges.length :=
      (CCL.Riemann.PreparedSheetContinuation.Subdivision.parameterEdges_length
        firstConnectorSubdivision).symm
    _ = (CCL.Riemann.ClearSheetContinuation.Subdivision.dyadicEdges 3
        CCL.Riemann.PreparedClearPathModels.zeroEndpoint
          CCL.Riemann.PreparedClearPathModels.oneEndpoint).length :=
      congrArg List.length firstConnectorSubdivisionParameterEdges
    _ = 2 ^ 3 :=
      CCL.Riemann.ClearSheetContinuation.Subdivision.dyadicEdges_length 3
      CCL.Riemann.PreparedClearPathModels.zeroEndpoint
        CCL.Riemann.PreparedClearPathModels.oneEndpoint

/-- The eight displayed requests are exactly the standard depth-three
dyadic request list, including the common root-diameter request. -/
theorem firstConnectorDyadicRequests :
    CCL.Riemann.PreparedSheetContinuation.Subdivision.dyadicRequests 3
      CCL.Riemann.PreparedClearPathModels.zeroEndpoint
        CCL.Riemann.PreparedClearPathModels.oneEndpoint workingRootDiameter
          workingRootDiameter_positive =
      [firstConnectorEdgeRequest 0, firstConnectorEdgeRequest 1,
        firstConnectorEdgeRequest 2, firstConnectorEdgeRequest 3,
        firstConnectorEdgeRequest 4, firstConnectorEdgeRequest 5,
        firstConnectorEdgeRequest 6, firstConnectorEdgeRequest 7] := by
  with_unfolding_all rfl

theorem firstConnectorTailEightRequests :
    firstConnectorTailEight.requests = [] := rfl

theorem firstConnectorTailSevenRequests :
    firstConnectorTailSeven.requests = [firstConnectorEdgeRequest 7] := by
  simp only [firstConnectorTailSeven,
    CCL.Riemann.PreparedSheetContinuation.Subdivision.nextCached_requests]
  exact congrArg (List.cons (firstConnectorEdgeRequest 7))
    firstConnectorTailEightRequests

theorem firstConnectorTailSixRequests :
    firstConnectorTailSix.requests =
      firstConnectorEdgeRequest 6 :: firstConnectorTailSeven.requests := by
  simp only [firstConnectorTailSix,
    CCL.Riemann.PreparedSheetContinuation.Subdivision.nextCached_requests]
  rfl

theorem firstConnectorTailFiveRequests :
    firstConnectorTailFive.requests =
      firstConnectorEdgeRequest 5 :: firstConnectorTailSix.requests := by
  simp only [firstConnectorTailFive,
    CCL.Riemann.PreparedSheetContinuation.Subdivision.nextCached_requests]
  rfl

theorem firstConnectorTailFourRequests :
    firstConnectorTailFour.requests =
      firstConnectorEdgeRequest 4 :: firstConnectorTailFive.requests := by
  simp only [firstConnectorTailFour,
    CCL.Riemann.PreparedSheetContinuation.Subdivision.nextCached_requests]
  rfl

theorem firstConnectorTailThreeRequests :
    firstConnectorTailThree.requests =
      firstConnectorEdgeRequest 3 :: firstConnectorTailFour.requests := by
  simp only [firstConnectorTailThree,
    CCL.Riemann.PreparedSheetContinuation.Subdivision.nextCached_requests]
  rfl

theorem firstConnectorTailTwoRequests :
    firstConnectorTailTwo.requests =
      firstConnectorEdgeRequest 2 :: firstConnectorTailThree.requests := by
  simp only [firstConnectorTailTwo,
    CCL.Riemann.PreparedSheetContinuation.Subdivision.nextCached_requests]
  rfl

theorem firstConnectorTailOneRequests :
    firstConnectorTailOne.requests =
      firstConnectorEdgeRequest 1 :: firstConnectorTailTwo.requests := by
  simp only [firstConnectorTailOne,
    CCL.Riemann.PreparedSheetContinuation.Subdivision.nextCached_requests]
  rfl

theorem firstConnectorSubdivisionRequests :
    firstConnectorSubdivision.requests =
      [firstConnectorEdgeRequest 0, firstConnectorEdgeRequest 1,
        firstConnectorEdgeRequest 2, firstConnectorEdgeRequest 3,
        firstConnectorEdgeRequest 4, firstConnectorEdgeRequest 5,
        firstConnectorEdgeRequest 6, firstConnectorEdgeRequest 7] := by
  calc
    firstConnectorSubdivision.requests =
        firstConnectorEdgeRequest 0 :: firstConnectorTailOne.requests := by
      simp only [firstConnectorSubdivision,
        CCL.Riemann.PreparedSheetContinuation.Subdivision.nextCached_requests]
      rfl
    _ = firstConnectorEdgeRequest 0 :: firstConnectorEdgeRequest 1 ::
        firstConnectorTailTwo.requests :=
      congrArg (List.cons (firstConnectorEdgeRequest 0))
        firstConnectorTailOneRequests
    _ = firstConnectorEdgeRequest 0 :: firstConnectorEdgeRequest 1 ::
        firstConnectorEdgeRequest 2 :: firstConnectorTailThree.requests :=
      congrArg (List.cons (firstConnectorEdgeRequest 0))
        (congrArg (List.cons (firstConnectorEdgeRequest 1))
          firstConnectorTailTwoRequests)
    _ = firstConnectorEdgeRequest 0 :: firstConnectorEdgeRequest 1 ::
        firstConnectorEdgeRequest 2 :: firstConnectorEdgeRequest 3 ::
          firstConnectorTailFour.requests :=
      congrArg (List.cons (firstConnectorEdgeRequest 0))
        (congrArg (List.cons (firstConnectorEdgeRequest 1))
          (congrArg (List.cons (firstConnectorEdgeRequest 2))
            firstConnectorTailThreeRequests))
    _ = firstConnectorEdgeRequest 0 :: firstConnectorEdgeRequest 1 ::
        firstConnectorEdgeRequest 2 :: firstConnectorEdgeRequest 3 ::
          firstConnectorEdgeRequest 4 :: firstConnectorTailFive.requests :=
      congrArg (List.cons (firstConnectorEdgeRequest 0))
        (congrArg (List.cons (firstConnectorEdgeRequest 1))
          (congrArg (List.cons (firstConnectorEdgeRequest 2))
            (congrArg (List.cons (firstConnectorEdgeRequest 3))
              firstConnectorTailFourRequests)))
    _ = firstConnectorEdgeRequest 0 :: firstConnectorEdgeRequest 1 ::
        firstConnectorEdgeRequest 2 :: firstConnectorEdgeRequest 3 ::
          firstConnectorEdgeRequest 4 :: firstConnectorEdgeRequest 5 ::
            firstConnectorTailSix.requests :=
      congrArg (List.cons (firstConnectorEdgeRequest 0))
        (congrArg (List.cons (firstConnectorEdgeRequest 1))
          (congrArg (List.cons (firstConnectorEdgeRequest 2))
            (congrArg (List.cons (firstConnectorEdgeRequest 3))
              (congrArg (List.cons (firstConnectorEdgeRequest 4))
                firstConnectorTailFiveRequests))))
    _ = firstConnectorEdgeRequest 0 :: firstConnectorEdgeRequest 1 ::
        firstConnectorEdgeRequest 2 :: firstConnectorEdgeRequest 3 ::
          firstConnectorEdgeRequest 4 :: firstConnectorEdgeRequest 5 ::
            firstConnectorEdgeRequest 6 :: firstConnectorTailSeven.requests :=
      congrArg (List.cons (firstConnectorEdgeRequest 0))
        (congrArg (List.cons (firstConnectorEdgeRequest 1))
          (congrArg (List.cons (firstConnectorEdgeRequest 2))
            (congrArg (List.cons (firstConnectorEdgeRequest 3))
              (congrArg (List.cons (firstConnectorEdgeRequest 4))
                (congrArg (List.cons (firstConnectorEdgeRequest 5))
                  firstConnectorTailSixRequests)))))
    _ = [firstConnectorEdgeRequest 0, firstConnectorEdgeRequest 1,
        firstConnectorEdgeRequest 2, firstConnectorEdgeRequest 3,
        firstConnectorEdgeRequest 4, firstConnectorEdgeRequest 5,
        firstConnectorEdgeRequest 6, firstConnectorEdgeRequest 7] :=
      congrArg (List.cons (firstConnectorEdgeRequest 0))
        (congrArg (List.cons (firstConnectorEdgeRequest 1))
          (congrArg (List.cons (firstConnectorEdgeRequest 2))
            (congrArg (List.cons (firstConnectorEdgeRequest 3))
              (congrArg (List.cons (firstConnectorEdgeRequest 4))
                (congrArg (List.cons (firstConnectorEdgeRequest 5))
                  (congrArg (List.cons (firstConnectorEdgeRequest 6))
                    firstConnectorTailSevenRequests))))))


/-! ## A directly certified dyadic path for the first connector cell -/

/-- The first outer connector cell as a one-segment clear path. -/
def firstConnectorCellPath :=
  CCL.Riemann.BranchCuts.ClearPath.cons firstConnectorSegment
    (CCL.Riemann.BranchCuts.ClearPath.nil
      (firstRawConnectorHeadData.head.pointAt (1 / 8)))

theorem firstConnectorCellPath_withinAmbient :
    firstConnectorCellPath.WithinAmbient :=
  .cons firstConnectorSegment_withinAmbient (.nil _)

/-- The complete cached continuation data for the first connector cell. -/
def firstConnectorCellPrepared :
    CCL.Riemann.PreparedClearPathModels.PreparedPath firstConnectorCellPath
      firstConnectorInputOwner :=
  .cons firstConnectorSegment
    (.nil (firstRawConnectorHeadData.head.pointAt (1 / 8)))
    firstConnectorInputOwner firstConnectorSegment_withinAmbient
      firstConnectorCompleteSegment
        (.nil (firstRawConnectorHeadData.head.pointAt (1 / 8))
          firstConnectorCompleteSegment.finishOwner)

/-- A direct finite certificate that the first connector cell uses precisely
the canonical depth-three mesh. -/
def firstConnectorCellCertifiedDyadic :
    CCL.Riemann.PreparedClearPathModels.PreparedPath.CertifiedDyadic 3
      workingRootDiameter workingRootDiameter_positive firstConnectorCellPath
        firstConnectorInputOwner where
  within := firstConnectorCellPath_withinAmbient
  prepared := firstConnectorCellPrepared
  generated := by
    change firstConnectorSubdivision.requests =
        CCL.Riemann.PreparedSheetContinuation.Subdivision.dyadicRequests 3
          CCL.Riemann.PreparedClearPathModels.zeroEndpoint
            CCL.Riemann.PreparedClearPathModels.oneEndpoint workingRootDiameter
              workingRootDiameter_positive ∧ True
    exact ⟨firstConnectorSubdivisionRequests.trans
      firstConnectorDyadicRequests.symm, trivial⟩
  prepared_allEdgesProper :=
    ⟨firstConnectorSubdivisionStrictParameterEdges, trivial⟩
  prepared_stepCount := by
    change firstConnectorSubdivision.stepCount + 0 =
      2 ^ 3 * firstConnectorCellPath.segmentCount
    rw [firstConnectorSubdivisionStepCount]
    unfold firstConnectorCellPath
    rfl
  prepared_toClearPath := by
    simp only [firstConnectorCellPrepared,
      CCL.Riemann.PreparedClearPathModels.PreparedPath.toClearPath]
    rw [CCL.Riemann.PreparedClearPathModels.CompleteSegment.clearPath_eq_dyadicRefineSegment_of_parameterEdges
      firstConnectorSegment
        firstConnectorSegment_withinAmbient firstConnectorInputOwner
          firstConnectorCompleteSegment 3
            firstConnectorSubdivisionParameterEdges]
    unfold firstConnectorCellPath
    have withinEqual : firstConnectorCellPath_withinAmbient =
        CCL.Riemann.BranchCuts.ClearPath.WithinAmbient.cons
          firstConnectorSegment_withinAmbient (.nil _) :=
      Subsingleton.elim _ _
    rw [withinEqual]
    rfl

end CCL.Riemann.ExplicitQuarticBranches
