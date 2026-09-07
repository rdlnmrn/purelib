import mathlib.Tactic.QuotientFreeOmega
import mathlib.Tactic.QuotientFreeRing
import RFAP.Winding.Global

/-!
# Choice-free winding of a Newton affine factor

The translated coordinate `Z-c` is represented by the exact two-coefficient
list `[1,-c]`.  Its four Cauchy indices are computed directly on the positive
square centered at `c`; multiplication by a nonzero constant slope is then
handled by the finite product formula.
-/

namespace RFAP.AffineWinding

abbrev Coordinate := RFAP.ConstructiveFraction.Rational
abbrev Gaussian := RFAP.ConstructiveGaussian.Gaussian
abbrev GaussianPolynomial := RFAP.ConstructivePolynomial.GaussianPolynomial
abbrev CoordinatePolynomial :=
  RFAP.ComputablePolynomial.DensePolynomial Coordinate
abbrev Box := RFAP.Boxes.Box

open RFAP.ConstructiveGaussian.Gaussian
open RFAP.ComputablePolynomial.DensePolynomial
open RFAP.PathPolynomial
open RFAP.Sturm
open RFAP.Winding
open RFAP.GlobalWinding

/-- Exact dense program for `Z-c`. -/
def translatedCoordinate (c : Gaussian) : GaussianPolynomial := ⟨[1, -c]⟩

@[simp] theorem translatedCoordinate_eval (c z : Gaussian) :
    (translatedCoordinate c).eval z = z - c := by
  simp only [translatedCoordinate, eval, evalCoeffs, List.foldl_cons,
    List.foldl_nil, zero_mul, zero_add, one_mul]
  exact (RFAP.ConstructiveGaussian.Gaussian.sub_eq_add_neg z c).symm

/-- Positive square of radius `r` centered at `c`. -/
def centeredSquare (c : Gaussian) (r : Coordinate)
    (nonnegative : 0 ≤ r) : Box where
  xLower := c.re - r
  xUpper := c.re + r
  yLower := c.im - r
  yUpper := c.im + r
  x_valid := by
    calc
      c.re - r = -r + c.re := by ring1
      _ = c.re + -r := by ring1
      _ ≤ c.re + r := add_le_add_right
        ((neg_nonpos.mpr nonnegative).trans nonnegative) c.re
      _ = c.re + r := by ring1
  y_valid := by
    calc
      c.im - r = -r + c.im := by ring1
      _ = c.im + -r := by ring1
      _ ≤ c.im + r := add_le_add_right
        ((neg_nonpos.mpr nonnegative).trans nonnegative) c.im
      _ = c.im + r := by ring1

theorem centeredSquare_proper (c : Gaussian) {r : Coordinate}
    (positive : 0 < r) : (centeredSquare c r positive.le).Proper := by
  constructor
  · calc
      c.re - r = -r + c.re := by ring1
      _ < r + c.re := RFAP.ConstructiveFraction.add_lt_add_right_direct
        ((neg_lt_zero.mpr positive).trans positive) c.re
      _ = c.re + r := by ring1
  · calc
      c.im - r = -r + c.im := by ring1
      _ < r + c.im := RFAP.ConstructiveFraction.add_lt_add_right_direct
        ((neg_lt_zero.mpr positive).trans positive) c.im
      _ = c.im + r := by ring1

/-- A smaller concentric positive square lies strictly inside a larger one. -/
theorem centeredSquare_strictInterior_of_lt
    (c : Gaussian) {inner outer : Coordinate}
    (innerNonnegative : 0 <= inner) (outerNonnegative : 0 <= outer)
    (strict : inner < outer) :
    (centeredSquare c inner innerNonnegative).StrictInterior
      (centeredSquare c outer outerNonnegative) := by
  constructor
  · change c.re - outer < c.re - inner
    have negated := RFAP.ConstructiveFraction.neg_lt_neg_direct strict
    calc
      c.re - outer = -outer + c.re := by ring1
      _ < -inner + c.re :=
        RFAP.ConstructiveFraction.add_lt_add_right_direct negated c.re
      _ = c.re - inner := by ring1
  · change c.re + inner < c.re + outer
    simpa only [RFAP.ConstructiveFraction.add_comm] using
      RFAP.ConstructiveFraction.add_lt_add_right_direct strict c.re
  · change c.im - outer < c.im - inner
    have negated := RFAP.ConstructiveFraction.neg_lt_neg_direct strict
    calc
      c.im - outer = -outer + c.im := by ring1
      _ < -inner + c.im :=
        RFAP.ConstructiveFraction.add_lt_add_right_direct negated c.im
      _ = c.im - inner := by ring1
  · change c.im + inner < c.im + outer
    simpa only [RFAP.ConstructiveFraction.add_comm] using
      RFAP.ConstructiveFraction.add_lt_add_right_direct strict c.im

theorem centeredSquare_diagonalSq (c : Gaussian) {r : Coordinate}
    (nonnegative : 0 ≤ r) :
    (centeredSquare c r nonnegative).diagonalSq = 8 * r ^ 2 := by
  dsimp only [centeredSquare, RFAP.Boxes.Box.diagonalSq]
  ring1

/-- A squared-norm bound gives the four coordinate bounds needed to place a
centered square, without introducing square roots. -/
theorem coordinate_bounds_of_normSq_le
    {z : Gaussian} {r : Coordinate} (nonnegative : 0 ≤ r)
    (bound : normSq z ≤ r ^ 2) :
    -r ≤ z.re ∧ z.re ≤ r ∧ -r ≤ z.im ∧ z.im ≤ r := by
  have realSquare : z.re ^ 2 ≤ r ^ 2 := by
    calc
      z.re ^ 2 = z.re ^ 2 + 0 := by ring1
      _ ≤ z.re ^ 2 + z.im ^ 2 :=
        add_le_add (le_refl _)
          (RFAP.ConstructiveFraction.sq_nonneg_direct z.im)
      _ ≤ r ^ 2 := bound
  have imaginarySquare : z.im ^ 2 ≤ r ^ 2 := by
    calc
      z.im ^ 2 = 0 + z.im ^ 2 := by ring1
      _ ≤ z.re ^ 2 + z.im ^ 2 :=
        add_le_add (RFAP.ConstructiveFraction.sq_nonneg_direct z.re)
          (le_refl _)
      _ ≤ r ^ 2 := bound
  have coordinateBounds : ∀ x : Coordinate, x ^ 2 ≤ r ^ 2 →
      -r ≤ x ∧ x ≤ r := by
    have nonnegativeUpper : ∀ {x : Coordinate}, 0 ≤ x →
        x ^ 2 ≤ r ^ 2 → x ≤ r := by
      intro x xNonnegative square
      by_cases upper : x ≤ r
      · exact upper
      · have strict : r < x := lt_of_not_ge upper
        have xPositive : 0 < x := nonnegative.trans_lt strict
        have first : r * r ≤ r * x :=
          RFAP.ConstructiveFraction.mul_le_mul_of_nonneg_left_direct
            strict.le nonnegative
        have second : r * x < x * x :=
          RFAP.ConstructiveFraction.mul_lt_mul_of_pos_right_direct
            strict xPositive
        have squaresStrict : r ^ 2 < x ^ 2 := by
          rw [pow_two, pow_two]
          exact first.trans_lt second
        exact (not_lt_of_ge square squaresStrict).elim
    intro x square
    by_cases xNonnegative : 0 ≤ x
    · exact ⟨(neg_nonpos.mpr nonnegative).trans xNonnegative,
        nonnegativeUpper xNonnegative square⟩
    · have xNonpositive : x ≤ 0 := le_of_not_ge xNonnegative
      have negXNonnegative : 0 ≤ -x := neg_nonneg.mpr xNonpositive
      have negSquare : (-x) ^ 2 = x ^ 2 := by ring1
      have negXLe : -x ≤ r :=
        nonnegativeUpper negXNonnegative (by
          rw [negSquare]
          exact square)
      exact ⟨by
          have := RFAP.ConstructiveFraction.neg_le_neg_direct negXLe
          simpa only [_root_.neg_neg] using this,
        xNonpositive.trans nonnegative⟩
  exact ⟨(coordinateBounds z.re realSquare).1,
    (coordinateBounds z.re realSquare).2,
    (coordinateBounds z.im imaginarySquare).1,
    (coordinateBounds z.im imaginarySquare).2⟩

/-- Every point of the centered square is within twice the squared radius of
its center. -/
theorem centeredSquare_normSq_sub_center_le
    (c : Gaussian) {r : Coordinate} (nonnegative : 0 ≤ r)
    {z : Gaussian} (inside : (centeredSquare c r nonnegative).Contains z) :
    normSq (z - c) ≤ 2 * r ^ 2 := by
  have xLower : -r ≤ z.re - c.re := by
    have shifted := RFAP.ConstructiveFraction.sub_le_sub_right_direct inside.1 c.re
    calc
      -r = c.re - r - c.re := by ring1
      _ ≤ z.re - c.re := shifted
  have xUpper : z.re - c.re ≤ r := by
    have shifted := RFAP.ConstructiveFraction.sub_le_sub_right_direct inside.2.1 c.re
    calc
      z.re - c.re ≤ c.re + r - c.re := shifted
      _ = r := by ring1
  have yLower : -r ≤ z.im - c.im := by
    have shifted := RFAP.ConstructiveFraction.sub_le_sub_right_direct inside.2.2.1 c.im
    calc
      -r = c.im - r - c.im := by ring1
      _ ≤ z.im - c.im := shifted
  have yUpper : z.im - c.im ≤ r := by
    have shifted := RFAP.ConstructiveFraction.sub_le_sub_right_direct inside.2.2.2 c.im
    calc
      z.im - c.im ≤ c.im + r - c.im := shifted
      _ = r := by ring1
  have xSquare := RFAP.Boxes.Box.sq_le_endpoint_max
    xLower xUpper
  have ySquare := RFAP.Boxes.Box.sq_le_endpoint_max
    yLower yUpper
  have negSquare : (-r) ^ 2 = r ^ 2 := by ring1
  rw [negSquare, max_self] at xSquare ySquare
  calc
    normSq (z - c) = (z.re - c.re) ^ 2 + (z.im - c.im) ^ 2 := rfl
    _ ≤ r ^ 2 + r ^ 2 := add_le_add xSquare ySquare
    _ = 2 * r ^ 2 := by ring1

private def affineVariable (center : Coordinate) : CoordinatePolynomial :=
  ⟨[1, -center]⟩

private def rawConstant (value : Coordinate) : CoordinatePolynomial :=
  ⟨[0, value]⟩

@[simp] private theorem affineVariable_eval (center t : Coordinate) :
    (affineVariable center).eval t = t - center := by
  simp only [affineVariable, eval, evalCoeffs, List.foldl_cons,
    List.foldl_nil]
  ring1

@[simp] private theorem rawConstant_eval (value t : Coordinate) :
    (rawConstant value).eval t = value := by
  simp [rawConstant, eval, evalCoeffs]

private theorem composeLine_translatedCoordinate
    (c origin direction : Gaussian) (directionNonzero : direction ≠ 0) :
    composeLine (translatedCoordinate c) origin direction =
      ⟨[direction, origin - c]⟩ := by
  have mulLineOne : mulLine origin direction (constant 1) =
      ⟨[direction, origin]⟩ := by
    rw [mulLine, scale_constant, scale_constant,
      RFAP.ConstructiveGaussian.Gaussian.mul_one,
      RFAP.ConstructiveGaussian.Gaussian.mul_one,
      normalize_constant_of_ne directionNonzero,
      shift_one_constant_of_ne directionNonzero]
    by_cases originZero : origin = 0
    · subst origin
      rw [normalize_constant_zero, zero_add_normalize,
        normalize_linear_of_leading_ne_zero directionNonzero]
    · rw [normalize_constant_of_ne originZero,
        constant_add_linear origin directionNonzero]
  rw [composeLine, composeLineCoeffs]
  simp only [translatedCoordinate, List.foldl_cons, List.foldl_nil]
  rw [mulLine_zero, zero_add_normalize,
    normalize_constant_of_ne one_ne_zero, mulLineOne,
    linear_add_constant origin (-c) directionNonzero]
  apply RFAP.ComputablePolynomial.DensePolynomial.ext
  simp only [sub_eq_add_neg]

private theorem translated_horizontal_real
    (c : Gaussian) (y a b : Coordinate) :
    (horizontalEdge (translatedCoordinate c) y a b).realPart =
      affineVariable c.re := by
  change realPart (composeLine (translatedCoordinate c)
      (horizontalBase y) horizontalDirection) = affineVariable c.re
  rw [composeLine_translatedCoordinate c
    (horizontalBase y) horizontalDirection (by
      intro equal
      have real := congrArg (fun z : Gaussian => z.re) equal
      change (1 : Coordinate) = 0 at real
      exact (Ne.symm RFAP.ConstructiveFraction.zero_ne_one) real)]
  apply RFAP.ComputablePolynomial.DensePolynomial.ext
  simp [realPart, affineVariable, horizontalDirection, horizontalBase]

private theorem translated_horizontal_imag
    (c : Gaussian) (y a b : Coordinate) :
    (horizontalEdge (translatedCoordinate c) y a b).imagPart =
      rawConstant (y - c.im) := by
  change imagPart (composeLine (translatedCoordinate c)
      (horizontalBase y) horizontalDirection) = rawConstant (y - c.im)
  rw [composeLine_translatedCoordinate c
    (horizontalBase y) horizontalDirection (by
      intro equal
      have real := congrArg (fun z : Gaussian => z.re) equal
      change (1 : Coordinate) = 0 at real
      exact (Ne.symm RFAP.ConstructiveFraction.zero_ne_one) real)]
  rfl

private theorem translated_vertical_real
    (c : Gaussian) (x a b : Coordinate) :
    (verticalEdge (translatedCoordinate c) x a b).realPart =
      rawConstant (x - c.re) := by
  change realPart (composeLine (translatedCoordinate c)
      (verticalBase x) verticalDirection) = rawConstant (x - c.re)
  rw [composeLine_translatedCoordinate c
    (verticalBase x) verticalDirection (by
      intro equal
      have imaginary := congrArg (fun z : Gaussian => z.im) equal
      change (1 : Coordinate) = 0 at imaginary
      exact (Ne.symm RFAP.ConstructiveFraction.zero_ne_one) imaginary)]
  apply RFAP.ComputablePolynomial.DensePolynomial.ext
  simp [realPart, rawConstant, verticalDirection, verticalBase]

private theorem translated_vertical_imag
    (c : Gaussian) (x a b : Coordinate) :
    (verticalEdge (translatedCoordinate c) x a b).imagPart =
      affineVariable c.im := by
  change imagPart (composeLine (translatedCoordinate c)
      (verticalBase x) verticalDirection) = affineVariable c.im
  rw [composeLine_translatedCoordinate c
    (verticalBase x) verticalDirection (by
      intro equal
      have imaginary := congrArg (fun z : Gaussian => z.im) equal
      change (1 : Coordinate) = 0 at imaginary
      exact (Ne.symm RFAP.ConstructiveFraction.zero_ne_one) imaginary)]
  apply RFAP.ComputablePolynomial.DensePolynomial.ext
  simp [imagPart, affineVariable, verticalDirection, verticalBase]

private theorem rawConstant_isZero_false {value : Coordinate}
    (nonzero : value ≠ 0) : (rawConstant value).isZero = false := by
  simp [rawConstant, isZero, normalize, nonzero]

private theorem rawConstant_degreeCount {value : Coordinate}
    (nonzero : value ≠ 0) : (rawConstant value).degreeCount = 1 := by
  simp [degreeCount, rawConstant, normalize, nonzero]

private theorem rawConstant_natDegree {value : Coordinate}
    (nonzero : value ≠ 0) : (rawConstant value).natDegree = 0 := by
  simp [natDegree, rawConstant_degreeCount nonzero]

private theorem rawConstant_normalize {value : Coordinate}
    (nonzero : value ≠ 0) :
    (rawConstant value).normalize = constant value := by
  apply RFAP.ComputablePolynomial.DensePolynomial.ext
  simp [rawConstant, normalize, constant, nonzero]

private theorem affineVariable_isZero_false (center : Coordinate) :
    (affineVariable center).isZero = false := by
  change (⟨[1, -center]⟩ : CoordinatePolynomial).isZero = false
  rw [isZero, normalize_linear_of_leading_ne_zero
    (Ne.symm RFAP.ConstructiveFraction.zero_ne_one)]
  rfl

private theorem affineVariable_degreeCount (center : Coordinate) :
    (affineVariable center).degreeCount = 2 := by
  change (⟨[1, -center]⟩ : CoordinatePolynomial).degreeCount = 2
  rw [degreeCount, normalize_linear_of_leading_ne_zero
    (Ne.symm RFAP.ConstructiveFraction.zero_ne_one)]
  rfl

private theorem affineVariable_natDegree (center : Coordinate) :
    (affineVariable center).natDegree = 1 := by
  simp [natDegree, affineVariable_degreeCount]

private theorem negNormalizedRawConstant_isZero_false {value : Coordinate}
    (nonzero : value ≠ 0) :
    (-((rawConstant value).normalize)).isZero = false := by
  simpa only [isZero_neg, isZero_normalize] using
    rawConstant_isZero_false nonzero

private theorem negNormalizedRawConstant_degreeCount {value : Coordinate}
    (nonzero : value ≠ 0) :
    (-((rawConstant value).normalize)).degreeCount = 1 := by
  simpa only [degreeCount_neg, degreeCount_normalize] using
    rawConstant_degreeCount nonzero

private theorem rawConstant_natDegree_lt_affineVariable
    {center value : Coordinate} (nonzero : value ≠ 0) :
    (rawConstant value).natDegree < (affineVariable center).natDegree := by
  calc
    (rawConstant value).natDegree = 0 := rawConstant_natDegree nonzero
    _ < 1 := Nat.zero_lt_succ 0
    _ = (affineVariable center).natDegree :=
      (affineVariable_natDegree center).symm

private theorem signedChain_rawConstant_affineVariable_cons
    {center value : Coordinate} (nonzero : value ≠ 0) :
    signedRemainderChain (rawConstant value) (affineVariable center) =
      rawConstant value :: signedRemainderChain (affineVariable center)
        (-((rawConstant value).normalize)) :=
  signedRemainderChain_eq_cons_of_degree_lt
    (rawConstant_isZero_false nonzero)
    (affineVariable_isZero_false center)
    (rawConstant_natDegree_lt_affineVariable nonzero)

private theorem signedChain_affineVariable_rawConstant
    {center value : Coordinate} (nonzero : value ≠ 0) :
    signedRemainderChain (affineVariable center) (rawConstant value) =
      [affineVariable center, rawConstant value] :=
  signedRemainderChain_eq_pair_of_second_degreeCount_one
    (rawConstant_isZero_false nonzero)
    (rawConstant_degreeCount nonzero)

private theorem signedChain_rawConstant_affineVariable
    {center value : Coordinate} (nonzero : value ≠ 0) :
    signedRemainderChain (rawConstant value) (affineVariable center) =
      [rawConstant value, affineVariable center,
        -((rawConstant value).normalize)] := by
  rw [signedChain_rawConstant_affineVariable_cons nonzero]
  rw [signedRemainderChain_eq_pair_of_second_degreeCount_one
    (negNormalizedRawConstant_isZero_false nonzero)
    (negNormalizedRawConstant_degreeCount nonzero)]

private theorem translated_bottom_winding
    (c : Gaussian) {r : Coordinate} (positive : 0 < r) :
    (horizontalEdge (translatedCoordinate c) (c.im - r)
      (c.re - r) (c.re + r)).doubledWinding = 0 := by
  rw [PolynomialEdge.doubledWinding,
    translated_horizontal_real, translated_horizontal_imag]
  change cauchyIndex2 (affineVariable c.re)
    (rawConstant (c.im - r - c.im)) (c.re - r) (c.re + r) = 0
  have negativeNonzero : c.im - r - c.im ≠ 0 := by
    have equality : c.im - r - c.im = -r := by ring1
    rw [equality]
    exact neg_ne_zero.mpr positive.ne'
  rw [cauchyIndex2,
    signedChain_rawConstant_affineVariable negativeNonzero,
    rawConstant_normalize negativeNonzero]
  simp only [endpointVariation2, List.map_cons, List.map_nil,
    rawConstant_eval, affineVariable_eval, eval_neg, eval_constant,
    variation2]
  have imaginaryValue : c.im - r - c.im = -r := by ring1
  have startValue : c.re - r - c.re = -r := by ring1
  have stopValue : c.re + r - c.re = r := by ring1
  rw [imaginaryValue, startValue, stopValue]
  simp only [_root_.neg_neg]
  rw [signJump_self, signJump_self]
  have opposite : (-r) * r < 0 := by
    rw [neg_mul]
    exact neg_neg_of_pos
      (RFAP.ConstructiveFraction.mul_pos_direct positive positive)
  rw [signJump_eq_two_of_mul_neg opposite]
  rfl

private theorem translated_top_winding
    (c : Gaussian) {r : Coordinate} (positive : 0 < r) :
    (horizontalEdge (translatedCoordinate c) (c.im + r)
      (c.re + r) (c.re - r)).doubledWinding = 0 := by
  rw [PolynomialEdge.doubledWinding,
    translated_horizontal_real, translated_horizontal_imag]
  change cauchyIndex2 (affineVariable c.re)
    (rawConstant (c.im + r - c.im)) (c.re + r) (c.re - r) = 0
  have nonzero : c.im + r - c.im ≠ 0 := by
    have equality : c.im + r - c.im = r := by ring1
    rw [equality]
    exact positive.ne'
  rw [cauchyIndex2,
    signedChain_rawConstant_affineVariable nonzero,
    rawConstant_normalize nonzero]
  simp only [endpointVariation2, List.map_cons, List.map_nil,
    rawConstant_eval, affineVariable_eval, eval_neg, eval_constant,
    variation2]
  have imaginaryValue : c.im + r - c.im = r := by ring1
  have startValue : c.re + r - c.re = r := by ring1
  have stopValue : c.re - r - c.re = -r := by ring1
  rw [imaginaryValue, startValue, stopValue]
  rw [signJump_self, signJump_self]
  have opposite : r * (-r) < 0 := by
    rw [mul_neg]
    exact neg_neg_of_pos
      (RFAP.ConstructiveFraction.mul_pos_direct positive positive)
  rw [signJump_eq_two_of_mul_neg opposite]
  rfl

private theorem translated_right_winding
    (c : Gaussian) {r : Coordinate} (positive : 0 < r) :
    (verticalEdge (translatedCoordinate c) (c.re + r)
      (c.im - r) (c.im + r)).doubledWinding = 2 := by
  rw [PolynomialEdge.doubledWinding,
    translated_vertical_real, translated_vertical_imag]
  change cauchyIndex2 (rawConstant (c.re + r - c.re))
    (affineVariable c.im) (c.im - r) (c.im + r) = 2
  have nonzero : c.re + r - c.re ≠ 0 := by
    have equality : c.re + r - c.re = r := by ring1
    rw [equality]
    exact positive.ne'
  rw [cauchyIndex2,
    signedChain_affineVariable_rawConstant nonzero]
  simp only [endpointVariation2, List.map_cons, List.map_nil,
    rawConstant_eval, affineVariable_eval, variation2]
  have realValue : c.re + r - c.re = r := by ring1
  have startValue : c.im - r - c.im = -r := by ring1
  have stopValue : c.im + r - c.im = r := by ring1
  rw [realValue, startValue, stopValue]
  rw [signJump_self]
  have opposite : (-r) * r < 0 := by
    rw [neg_mul]
    exact neg_neg_of_pos
      (RFAP.ConstructiveFraction.mul_pos_direct positive positive)
  rw [signJump_eq_two_of_mul_neg opposite]
  rfl

private theorem translated_left_winding
    (c : Gaussian) {r : Coordinate} (positive : 0 < r) :
    (verticalEdge (translatedCoordinate c) (c.re - r)
      (c.im + r) (c.im - r)).doubledWinding = 2 := by
  rw [PolynomialEdge.doubledWinding,
    translated_vertical_real, translated_vertical_imag]
  change cauchyIndex2 (rawConstant (c.re - r - c.re))
    (affineVariable c.im) (c.im + r) (c.im - r) = 2
  have nonzero : c.re - r - c.re ≠ 0 := by
    have equality : c.re - r - c.re = -r := by ring1
    rw [equality]
    exact neg_ne_zero.mpr positive.ne'
  rw [cauchyIndex2,
    signedChain_affineVariable_rawConstant nonzero]
  simp only [endpointVariation2, List.map_cons, List.map_nil,
    rawConstant_eval, affineVariable_eval, variation2]
  have realValue : c.re - r - c.re = -r := by ring1
  have startValue : c.im + r - c.im = r := by ring1
  have stopValue : c.im - r - c.im = -r := by ring1
  rw [realValue, startValue, stopValue]
  rw [signJump_self]
  have opposite : r * (-r) < 0 := by
    rw [mul_neg]
    exact neg_neg_of_pos
      (RFAP.ConstructiveFraction.mul_pos_direct positive positive)
  rw [signJump_eq_two_of_mul_neg opposite]
  rfl

private theorem translated_bottom_winding_box
    (c : Gaussian) {box : Box}
    (left : box.xLower < c.re) (right : c.re < box.xUpper)
    (below : box.yLower < c.im) :
    (horizontalEdge (translatedCoordinate c) box.yLower
      box.xLower box.xUpper).doubledWinding = 0 := by
  rw [PolynomialEdge.doubledWinding,
    translated_horizontal_real, translated_horizontal_imag]
  change cauchyIndex2 (affineVariable c.re)
    (rawConstant (box.yLower - c.im)) box.xLower box.xUpper = 0
  have imaginaryNonzero : box.yLower - c.im ≠ 0 :=
    sub_ne_zero.mpr (ne_of_lt below)
  rw [cauchyIndex2,
    signedChain_rawConstant_affineVariable imaginaryNonzero,
    rawConstant_normalize imaginaryNonzero]
  simp only [endpointVariation2, List.map_cons, List.map_nil,
    rawConstant_eval, affineVariable_eval, eval_neg, eval_constant,
    variation2]
  have qNegative : box.yLower - c.im < 0 :=
    RFAP.ConstructiveFraction.sub_neg_direct below
  have negQPositive : 0 < -(box.yLower - c.im) := neg_pos.mpr qNegative
  have leftNegative : box.xLower - c.re < 0 :=
    RFAP.ConstructiveFraction.sub_neg_direct left
  have rightPositive : 0 < box.xUpper - c.re :=
    RFAP.ConstructiveFraction.sub_pos_direct right
  rw [signJump_eq_zero_of_mul_pos
      (RFAP.ConstructiveFraction.mul_pos_of_neg_of_neg_direct
        qNegative leftNegative),
    signJump_eq_two_of_mul_neg
      (RFAP.ConstructiveFraction.mul_neg_of_neg_of_pos_direct
        leftNegative negQPositive),
    signJump_eq_two_of_mul_neg
      (RFAP.ConstructiveFraction.mul_neg_of_neg_of_pos_direct
        qNegative rightPositive),
    signJump_eq_zero_of_mul_pos
      (RFAP.ConstructiveFraction.mul_pos_direct rightPositive negQPositive)]
  rfl

private theorem translated_top_winding_box
    (c : Gaussian) {box : Box}
    (left : box.xLower < c.re) (right : c.re < box.xUpper)
    (above : c.im < box.yUpper) :
    (horizontalEdge (translatedCoordinate c) box.yUpper
      box.xUpper box.xLower).doubledWinding = 0 := by
  rw [PolynomialEdge.doubledWinding,
    translated_horizontal_real, translated_horizontal_imag]
  change cauchyIndex2 (affineVariable c.re)
    (rawConstant (box.yUpper - c.im)) box.xUpper box.xLower = 0
  have imaginaryNonzero : box.yUpper - c.im ≠ 0 :=
    sub_ne_zero.mpr (ne_of_gt above)
  rw [cauchyIndex2,
    signedChain_rawConstant_affineVariable imaginaryNonzero,
    rawConstant_normalize imaginaryNonzero]
  simp only [endpointVariation2, List.map_cons, List.map_nil,
    rawConstant_eval, affineVariable_eval, eval_neg, eval_constant,
    variation2]
  have qPositive : 0 < box.yUpper - c.im :=
    RFAP.ConstructiveFraction.sub_pos_direct above
  have negQNegative : -(box.yUpper - c.im) < 0 := neg_neg_of_pos qPositive
  have leftNegative : box.xLower - c.re < 0 :=
    RFAP.ConstructiveFraction.sub_neg_direct left
  have rightPositive : 0 < box.xUpper - c.re :=
    RFAP.ConstructiveFraction.sub_pos_direct right
  rw [signJump_eq_zero_of_mul_pos
      (RFAP.ConstructiveFraction.mul_pos_direct qPositive rightPositive),
    signJump_eq_two_of_mul_neg
      (RFAP.ConstructiveFraction.mul_neg_of_pos_of_neg_direct
        rightPositive negQNegative),
    signJump_eq_two_of_mul_neg
      (RFAP.ConstructiveFraction.mul_neg_of_pos_of_neg_direct
        qPositive leftNegative),
    signJump_eq_zero_of_mul_pos
      (RFAP.ConstructiveFraction.mul_pos_of_neg_of_neg_direct
        leftNegative negQNegative)]
  rfl

private theorem translated_right_winding_box
    (c : Gaussian) {box : Box}
    (right : c.re < box.xUpper)
    (below : box.yLower < c.im) (above : c.im < box.yUpper) :
    (verticalEdge (translatedCoordinate c) box.xUpper
      box.yLower box.yUpper).doubledWinding = 2 := by
  rw [PolynomialEdge.doubledWinding,
    translated_vertical_real, translated_vertical_imag]
  change cauchyIndex2 (rawConstant (box.xUpper - c.re))
    (affineVariable c.im) box.yLower box.yUpper = 2
  have realNonzero : box.xUpper - c.re ≠ 0 :=
    sub_ne_zero.mpr (ne_of_gt right)
  rw [cauchyIndex2, signedChain_affineVariable_rawConstant realNonzero]
  simp only [endpointVariation2, List.map_cons, List.map_nil,
    rawConstant_eval, affineVariable_eval, variation2]
  have realPositive : 0 < box.xUpper - c.re :=
    RFAP.ConstructiveFraction.sub_pos_direct right
  have lowerNegative : box.yLower - c.im < 0 :=
    RFAP.ConstructiveFraction.sub_neg_direct below
  have upperPositive : 0 < box.yUpper - c.im :=
    RFAP.ConstructiveFraction.sub_pos_direct above
  rw [signJump_eq_two_of_mul_neg
      (RFAP.ConstructiveFraction.mul_neg_of_neg_of_pos_direct
        lowerNegative realPositive),
    signJump_eq_zero_of_mul_pos
      (RFAP.ConstructiveFraction.mul_pos_direct upperPositive realPositive)]
  rfl

private theorem translated_left_winding_box
    (c : Gaussian) {box : Box}
    (left : box.xLower < c.re)
    (below : box.yLower < c.im) (above : c.im < box.yUpper) :
    (verticalEdge (translatedCoordinate c) box.xLower
      box.yUpper box.yLower).doubledWinding = 2 := by
  rw [PolynomialEdge.doubledWinding,
    translated_vertical_real, translated_vertical_imag]
  change cauchyIndex2 (rawConstant (box.xLower - c.re))
    (affineVariable c.im) box.yUpper box.yLower = 2
  have realNonzero : box.xLower - c.re ≠ 0 :=
    sub_ne_zero.mpr (ne_of_lt left)
  rw [cauchyIndex2, signedChain_affineVariable_rawConstant realNonzero]
  simp only [endpointVariation2, List.map_cons, List.map_nil,
    rawConstant_eval, affineVariable_eval, variation2]
  have realNegative : box.xLower - c.re < 0 :=
    RFAP.ConstructiveFraction.sub_neg_direct left
  have lowerNegative : box.yLower - c.im < 0 :=
    RFAP.ConstructiveFraction.sub_neg_direct below
  have upperPositive : 0 < box.yUpper - c.im :=
    RFAP.ConstructiveFraction.sub_pos_direct above
  rw [signJump_eq_two_of_mul_neg
      (RFAP.ConstructiveFraction.mul_neg_of_pos_of_neg_direct
        upperPositive realNegative),
    signJump_eq_zero_of_mul_pos
      (RFAP.ConstructiveFraction.mul_pos_of_neg_of_neg_direct
        lowerNegative realNegative)]
  rfl

/-- Direct finite Cauchy-index normalization for a translated coordinate on
any proper rational rectangle whose strict interior contains its center. -/
theorem quadrupledBoxWinding_translatedCoordinate
    (c : Gaussian) {box : Box}
    (left : box.xLower < c.re) (right : c.re < box.xUpper)
    (below : box.yLower < c.im) (above : c.im < box.yUpper) :
    quadrupledBoxWinding (translatedCoordinate c) box = 4 := by
  rw [quadrupledBoxWinding_eq,
    translated_bottom_winding_box c left right below,
    translated_right_winding_box c right below above,
    translated_top_winding_box c left right above,
    translated_left_winding_box c left below above]
  rfl

theorem quadrupledBoxWinding_translatedCoordinate_centeredSquare
    (c : Gaussian) {r : Coordinate} (positive : 0 < r) :
    quadrupledBoxWinding (translatedCoordinate c)
      (centeredSquare c r positive.le) = 4 := by
  rw [quadrupledBoxWinding_eq]
  dsimp only [centeredSquare]
  rw [translated_bottom_winding c positive,
    translated_right_winding c positive,
    translated_top_winding c positive,
    translated_left_winding c positive]
  ring1

def translatedCoordinate_boundaryClearance
    (c : Gaussian) {r : Coordinate} (positive : 0 < r) :
    RFAP.BoxClearance.BoundaryClearance
      (translatedCoordinate c) (centeredSquare c r positive.le) where
  bound := r ^ 2
  positive := RFAP.ConstructiveFraction.pow_pos_direct positive 2
  lower := by
    intro z boundary
    rw [translatedCoordinate_eval]
    change r ^ 2 ≤ (z.re - c.re) ^ 2 + (z.im - c.im) ^ 2
    rcases boundary.2 with left | right | bottom | top
    · change z.re = c.re - r at left
      rw [left]
      have first : (c.re - r - c.re) ^ 2 = r ^ 2 := by ring1
      rw [first]
      exact le_add_of_nonneg_right
        (RFAP.ConstructiveFraction.sq_nonneg_direct _)
    · change z.re = c.re + r at right
      rw [right]
      have first : (c.re + r - c.re) ^ 2 = r ^ 2 := by ring1
      rw [first]
      exact le_add_of_nonneg_right
        (RFAP.ConstructiveFraction.sq_nonneg_direct _)
    · change z.im = c.im - r at bottom
      rw [bottom]
      have second : (c.im - r - c.im) ^ 2 = r ^ 2 := by ring1
      rw [second]
      exact le_add_of_nonneg_left
        (RFAP.ConstructiveFraction.sq_nonneg_direct _)
    · change z.im = c.im + r at top
      rw [top]
      have second : (c.im + r - c.im) ^ 2 = r ^ 2 := by ring1
      rw [second]
      exact le_add_of_nonneg_left
        (RFAP.ConstructiveFraction.sq_nonneg_direct _)

/-- Quantitative clearance of `Z-c` on any rational rectangle whose strict
interior contains `c`. -/
def translatedCoordinate_boundaryClearanceBox
    (c : Gaussian) {box : Box}
    (left : box.xLower < c.re) (right : c.re < box.xUpper)
    (below : box.yLower < c.im) (above : c.im < box.yUpper) :
    RFAP.BoxClearance.BoundaryClearance
      (translatedCoordinate c) box where
  bound := min ((c.re - box.xLower) ^ 2)
    (min ((box.xUpper - c.re) ^ 2)
      (min ((c.im - box.yLower) ^ 2) ((box.yUpper - c.im) ^ 2)))
  positive := lt_min
    (RFAP.ConstructiveFraction.pow_pos_direct
      (RFAP.ConstructiveFraction.sub_pos_direct left) 2)
    (lt_min
      (RFAP.ConstructiveFraction.pow_pos_direct
        (RFAP.ConstructiveFraction.sub_pos_direct right) 2)
      (lt_min
        (RFAP.ConstructiveFraction.pow_pos_direct
          (RFAP.ConstructiveFraction.sub_pos_direct below) 2)
        (RFAP.ConstructiveFraction.pow_pos_direct
          (RFAP.ConstructiveFraction.sub_pos_direct above) 2)))
  lower := by
    intro z boundary
    rw [translatedCoordinate_eval]
    change min ((c.re - box.xLower) ^ 2)
        (min ((box.xUpper - c.re) ^ 2)
          (min ((c.im - box.yLower) ^ 2) ((box.yUpper - c.im) ^ 2))) ≤
      (z.re - c.re) ^ 2 + (z.im - c.im) ^ 2
    rcases boundary.2 with onLeft | onRight | onBottom | onTop
    · have selected : min ((c.re - box.xLower) ^ 2)
          (min ((box.xUpper - c.re) ^ 2)
            (min ((c.im - box.yLower) ^ 2)
              ((box.yUpper - c.im) ^ 2))) ≤
          (c.re - box.xLower) ^ 2 := min_le_left _ _
      calc
        _ ≤ (c.re - box.xLower) ^ 2 := selected
        _ = (z.re - c.re) ^ 2 := by rw [onLeft]; ring1
        _ ≤ (z.re - c.re) ^ 2 + (z.im - c.im) ^ 2 :=
          le_add_of_nonneg_right
            (RFAP.ConstructiveFraction.sq_nonneg_direct _)
    · have selected : min ((c.re - box.xLower) ^ 2)
          (min ((box.xUpper - c.re) ^ 2)
            (min ((c.im - box.yLower) ^ 2)
              ((box.yUpper - c.im) ^ 2))) ≤
          (box.xUpper - c.re) ^ 2 :=
        (min_le_right _ _).trans (min_le_left _ _)
      calc
        _ ≤ (box.xUpper - c.re) ^ 2 := selected
        _ = (z.re - c.re) ^ 2 := by rw [onRight]
        _ ≤ (z.re - c.re) ^ 2 + (z.im - c.im) ^ 2 :=
          le_add_of_nonneg_right
            (RFAP.ConstructiveFraction.sq_nonneg_direct _)
    · have selected : min ((c.re - box.xLower) ^ 2)
          (min ((box.xUpper - c.re) ^ 2)
            (min ((c.im - box.yLower) ^ 2)
              ((box.yUpper - c.im) ^ 2))) ≤
          (c.im - box.yLower) ^ 2 :=
        (min_le_right _ _).trans
          ((min_le_right _ _).trans (min_le_left _ _))
      calc
        _ ≤ (c.im - box.yLower) ^ 2 := selected
        _ = (z.im - c.im) ^ 2 := by rw [onBottom]; ring1
        _ ≤ (z.re - c.re) ^ 2 + (z.im - c.im) ^ 2 :=
          le_add_of_nonneg_left
            (RFAP.ConstructiveFraction.sq_nonneg_direct _)
    · have selected : min ((c.re - box.xLower) ^ 2)
          (min ((box.xUpper - c.re) ^ 2)
            (min ((c.im - box.yLower) ^ 2)
              ((box.yUpper - c.im) ^ 2))) ≤
          (box.yUpper - c.im) ^ 2 :=
        (min_le_right _ _).trans
          ((min_le_right _ _).trans (min_le_right _ _))
      calc
        _ ≤ (box.yUpper - c.im) ^ 2 := selected
        _ = (z.im - c.im) ^ 2 := by rw [onTop]
        _ ≤ (z.re - c.re) ^ 2 + (z.im - c.im) ^ 2 :=
          le_add_of_nonneg_left
            (RFAP.ConstructiveFraction.sq_nonneg_direct _)

/-- Quantitative clearance of `Z-c` on a box lying strictly to the right of
`c`.  Real-coordinate separation alone supplies the positive lower bound. -/
def translatedCoordinate_boundaryClearance_of_left
    (c : Gaussian) {box : Box} (left : c.re < box.xLower) :
    RFAP.BoxClearance.BoundaryClearance
      (translatedCoordinate c) box where
  bound := (box.xLower - c.re) ^ 2
  positive := RFAP.ConstructiveFraction.pow_pos_direct
    (RFAP.ConstructiveFraction.sub_pos_direct left) 2
  lower := by
    intro z boundary
    rw [translatedCoordinate_eval]
    change (box.xLower - c.re) ^ 2 ≤
      (z.re - c.re) ^ 2 + (z.im - c.im) ^ 2
    have shifted : box.xLower - c.re ≤ z.re - c.re :=
      RFAP.ConstructiveFraction.sub_le_sub_right_direct boundary.1.1 c.re
    have square : (box.xLower - c.re) ^ 2 ≤ (z.re - c.re) ^ 2 :=
      RFAP.ConstructiveFraction.pow_le_pow_direct
        (RFAP.ConstructiveFraction.sub_nonneg_direct left.le) shifted 2
    exact square.trans (le_add_of_nonneg_right
      (RFAP.ConstructiveFraction.sq_nonneg_direct _))

/-- Quantitative clearance of `Z-c` on a box lying strictly to the left of
`c`.  This is the reflected companion of
`translatedCoordinate_boundaryClearance_of_left`. -/
def translatedCoordinate_boundaryClearance_of_right
    (c : Gaussian) {box : Box} (right : box.xUpper < c.re) :
    RFAP.BoxClearance.BoundaryClearance
      (translatedCoordinate c) box where
  bound := (c.re - box.xUpper) ^ 2
  positive := RFAP.ConstructiveFraction.pow_pos_direct
    (RFAP.ConstructiveFraction.sub_pos_direct right) 2
  lower := by
    intro z boundary
    rw [translatedCoordinate_eval]
    change (c.re - box.xUpper) ^ 2 ≤
      (z.re - c.re) ^ 2 + (z.im - c.im) ^ 2
    have shifted : c.re - box.xUpper ≤ c.re - z.re :=
      RFAP.ConstructiveFraction.sub_le_sub_left_direct boundary.1.2.1 c.re
    have square : (c.re - box.xUpper) ^ 2 ≤ (c.re - z.re) ^ 2 :=
      RFAP.ConstructiveFraction.pow_le_pow_direct
        (RFAP.ConstructiveFraction.sub_nonneg_direct right.le) shifted 2
    have reflected : (c.re - z.re) ^ 2 = (z.re - c.re) ^ 2 := by ring1
    rw [reflected] at square
    exact square.trans (le_add_of_nonneg_right
      (RFAP.ConstructiveFraction.sq_nonneg_direct _))

/-- Quantitative clearance of `Z-c` on a box lying strictly above `c`. -/
def translatedCoordinate_boundaryClearance_of_below
    (c : Gaussian) {box : Box} (below : c.im < box.yLower) :
    RFAP.BoxClearance.BoundaryClearance
      (translatedCoordinate c) box where
  bound := (box.yLower - c.im) ^ 2
  positive := RFAP.ConstructiveFraction.pow_pos_direct
    (RFAP.ConstructiveFraction.sub_pos_direct below) 2
  lower := by
    intro z boundary
    rw [translatedCoordinate_eval]
    change (box.yLower - c.im) ^ 2 ≤
      (z.re - c.re) ^ 2 + (z.im - c.im) ^ 2
    have shifted : box.yLower - c.im ≤ z.im - c.im :=
      RFAP.ConstructiveFraction.sub_le_sub_right_direct boundary.1.2.2.1 c.im
    have square : (box.yLower - c.im) ^ 2 ≤ (z.im - c.im) ^ 2 :=
      RFAP.ConstructiveFraction.pow_le_pow_direct
        (RFAP.ConstructiveFraction.sub_nonneg_direct below.le) shifted 2
    exact square.trans (le_add_of_nonneg_left
      (RFAP.ConstructiveFraction.sq_nonneg_direct _))

/-- Quantitative clearance of `Z-c` on a box lying strictly below `c`. -/
def translatedCoordinate_boundaryClearance_of_above
    (c : Gaussian) {box : Box} (above : box.yUpper < c.im) :
    RFAP.BoxClearance.BoundaryClearance
      (translatedCoordinate c) box where
  bound := (c.im - box.yUpper) ^ 2
  positive := RFAP.ConstructiveFraction.pow_pos_direct
    (RFAP.ConstructiveFraction.sub_pos_direct above) 2
  lower := by
    intro z boundary
    rw [translatedCoordinate_eval]
    change (c.im - box.yUpper) ^ 2 ≤
      (z.re - c.re) ^ 2 + (z.im - c.im) ^ 2
    have shifted : c.im - box.yUpper ≤ c.im - z.im :=
      RFAP.ConstructiveFraction.sub_le_sub_left_direct boundary.1.2.2.2 c.im
    have square : (c.im - box.yUpper) ^ 2 ≤ (c.im - z.im) ^ 2 :=
      RFAP.ConstructiveFraction.pow_le_pow_direct
        (RFAP.ConstructiveFraction.sub_nonneg_direct above.le) shifted 2
    have reflected : (c.im - z.im) ^ 2 = (z.im - c.im) ^ 2 := by ring1
    rw [reflected] at square
    exact square.trans (le_add_of_nonneg_left
      (RFAP.ConstructiveFraction.sq_nonneg_direct _))

private theorem coordinate_sq_pos_of_ne_zero {value : Coordinate}
    (nonzero : value ≠ 0) : 0 < value ^ 2 := by
  have squareNonzero : value ^ 2 ≠ 0 := by
    intro zero
    exact nonzero ((RFAP.ConstructiveFraction.sq_eq_zero_direct value).mp zero)
  exact lt_of_le_of_ne (RFAP.ConstructiveFraction.sq_nonneg_direct value)
    (Ne.symm squareNonzero)

/-- Quantitative clearance of `Z-c` on an entire displayed vertical line.
The fixed real-coordinate gap supplies the lower bound independently of the
ambient vertical interval. -/
def translatedCoordinate_verticalLineClearance
    (c : Gaussian) (ambient : Box) (x : Coordinate)
    (apart : x ≠ c.re) :
    RFAP.BoxClearance.VerticalLineClearance
      (translatedCoordinate c) ambient x where
  bound := (x - c.re) ^ 2
  positive := coordinate_sq_pos_of_ne_zero (sub_ne_zero.mpr apart)
  lower := by
    intro y lower upper
    rw [translatedCoordinate_eval]
    change (x - c.re) ^ 2 <=
      (x - c.re) ^ 2 + (y - c.im) ^ 2
    exact le_add_of_nonneg_right
      (RFAP.ConstructiveFraction.sq_nonneg_direct _)

/-- Horizontal companion of
`translatedCoordinate_verticalLineClearance`. -/
def translatedCoordinate_horizontalLineClearance
    (c : Gaussian) (ambient : Box) (y : Coordinate)
    (apart : y ≠ c.im) :
    RFAP.BoxClearance.HorizontalLineClearance
      (translatedCoordinate c) ambient y where
  bound := (y - c.im) ^ 2
  positive := coordinate_sq_pos_of_ne_zero (sub_ne_zero.mpr apart)
  lower := by
    intro x lower upper
    rw [translatedCoordinate_eval]
    change (y - c.im) ^ 2 <=
      (x - c.re) ^ 2 + (y - c.im) ^ 2
    exact le_add_of_nonneg_left
      (RFAP.ConstructiveFraction.sq_nonneg_direct _)

/-- Executable affine linear program `s(Z-c)`. -/
def affineCoordinate (s c : Gaussian) : GaussianPolynomial :=
  gaussianConstant s * translatedCoordinate c

/-- Exact two-coefficient representation of the affine program. -/
theorem affineCoordinate_eq_linear
    {s : Gaussian} (slopeNonzero : s ≠ 0) (c : Gaussian) :
    affineCoordinate s c = ⟨[s, -(s * c)]⟩ := by
  rw [affineCoordinate, gaussianConstant]
  change mulPolynomial (constant s) (translatedCoordinate c) =
    ⟨[s, -(s * c)]⟩
  rw [mulPolynomial]
  simp only [constant_coeffs, List.foldl_cons, List.foldl_nil]
  rw [shift_zero, zero_add_normalize, normalize_scale]
  apply RFAP.ComputablePolynomial.DensePolynomial.ext
  rw [scale_coeffs_of_ne_zero slopeNonzero]
  simp only [translatedCoordinate, normalize_coeffs, List.dropWhile]
  apply congrArg₂ List.cons (by
    exact RFAP.ConstructiveGaussian.Gaussian.mul_one s)
  apply congrArg₂ List.cons (by
    apply RFAP.ConstructiveGaussian.Gaussian.ext <;>
      simp only [mul_re, mul_im, neg_re, neg_im] <;>
      ring1) rfl

@[simp] theorem affineCoordinate_eval (s c z : Gaussian) :
    (affineCoordinate s c).eval z = s * (z - c) := by
  rw [affineCoordinate, eval_mul, gaussianConstant_eval,
    translatedCoordinate_eval]

/-- Exact quantitative clearance of a nonzero affine factor on a centered
square. -/
def affineCoordinate_boundaryClearance
    {s : Gaussian} (slopeNonzero : s ≠ 0) (c : Gaussian)
    {r : Coordinate} (positive : 0 < r) :
    RFAP.BoxClearance.BoundaryClearance
      (affineCoordinate s c) (centeredSquare c r positive.le) := by
  exact (gaussianConstant_boundaryClearance slopeNonzero
    (centeredSquare c r positive.le)).mul
      (translatedCoordinate_boundaryClearance c positive)

/-- Quantitative clearance of a nonzero affine factor on an arbitrary
rectangle whose strict interior contains its zero. -/
def affineCoordinate_boundaryClearanceBox
    {s : Gaussian} (slopeNonzero : s ≠ 0) (c : Gaussian) {box : Box}
    (left : box.xLower < c.re) (right : c.re < box.xUpper)
    (below : box.yLower < c.im) (above : c.im < box.yUpper) :
    RFAP.BoxClearance.BoundaryClearance
      (affineCoordinate s c) box :=
  (gaussianConstant_boundaryClearance slopeNonzero box).mul
    (translatedCoordinate_boundaryClearanceBox c left right below above)

/-- A nonzero slope preserves winding four on every rational rectangle whose
strict interior contains the affine zero. -/
theorem quadrupledBoxWinding_affineCoordinate
    {s : Gaussian} (slopeNonzero : s ≠ 0) (c : Gaussian) {box : Box}
    (left : box.xLower < c.re) (right : c.re < box.xUpper)
    (below : box.yLower < c.im) (above : c.im < box.yUpper) :
    quadrupledBoxWinding (affineCoordinate s c) box = 4 := by
  have proper : box.Proper :=
    ⟨left.trans right, below.trans above⟩
  have product :=
    RFAP.WindingProduct.quadrupledBoxWinding_mul_of_boundaryClearances
      (gaussianConstant s) (translatedCoordinate c) box proper
      (gaussianConstant_boundaryClearance slopeNonzero box)
      (translatedCoordinate_boundaryClearanceBox c left right below above)
  rw [quadrupledBoxWinding_gaussianConstant slopeNonzero,
    quadrupledBoxWinding_translatedCoordinate c left right below above]
    at product
  exact product

/-- A nonzero slope preserves the raw winding-four normalization. -/
theorem quadrupledBoxWinding_affineCoordinate_centeredSquare
    {s : Gaussian} (slopeNonzero : s ≠ 0) (c : Gaussian)
    {r : Coordinate} (positive : 0 < r) :
    quadrupledBoxWinding (affineCoordinate s c)
      (centeredSquare c r positive.le) = 4 := by
  have product :=
    RFAP.WindingProduct.quadrupledBoxWinding_mul_of_boundaryClearances
      (gaussianConstant s) (translatedCoordinate c)
      (centeredSquare c r positive.le) (centeredSquare_proper c positive)
      (gaussianConstant_boundaryClearance slopeNonzero _)
      (translatedCoordinate_boundaryClearance c positive)
  rw [quadrupledBoxWinding_gaussianConstant slopeNonzero,
    quadrupledBoxWinding_translatedCoordinate_centeredSquare c positive]
    at product
  exact product

end RFAP.AffineWinding
