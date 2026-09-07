import mathlib.Data.ConstructiveList
import mathlib.Tactic.QuotientFreeOmega
import mathlib.Tactic.QuotientFreeRing
import RFAP.Polynomial.Bounds
import mathlib.RFAP.ConstructiveFiniteNorm
import RFAP.Winding.Product
import RFAP.Winding.Homotopy

/-!
# Choice-free global winding on a finite constructive square

This module develops the coefficient-computed large-square theorem entirely
over the explicit constructive fraction and Gaussian representations.  Its
first layer computes the winding of the coordinate polynomial symbolically;
later layers transfer that value to a general positive-degree polynomial.
-/

namespace RFAP.GlobalWinding

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

/-- The executable coordinate polynomial `Z`. -/
def coordinatePolynomial : GaussianPolynomial := ⟨[1, 0]⟩

private def coordinateOne : CoordinatePolynomial := ⟨[1]⟩
private def coordinateVariable : CoordinatePolynomial := ⟨[1, 0]⟩
private def rawLinearConstant (c : Coordinate) : CoordinatePolynomial :=
  ⟨[0, c]⟩

@[simp] theorem coordinatePolynomial_eval (z : Gaussian) :
    coordinatePolynomial.eval z = z := by
  simp [coordinatePolynomial, eval, evalCoeffs]

private theorem coordinateOne_eval (t : Coordinate) :
    coordinateOne.eval t = 1 := by
  simp [coordinateOne, eval, evalCoeffs]

private theorem coordinateVariable_eval (t : Coordinate) :
    coordinateVariable.eval t = t := by
  simp [coordinateVariable, eval, evalCoeffs]

private theorem composeLine_coordinate (origin direction : Gaussian)
    (directionNonzero : direction ≠ 0) :
    composeLine coordinatePolynomial origin direction =
      ⟨[direction, origin]⟩ := by
  rw [composeLine, composeLineCoeffs]
  simp only [coordinatePolynomial, List.foldl_cons, List.foldl_nil]
  rw [mulLine_zero, zero_add_normalize,
    normalize_constant_of_ne one_ne_zero]
  rw [mulLine, scale_constant, scale_constant,
    RFAP.ConstructiveGaussian.Gaussian.mul_one,
    RFAP.ConstructiveGaussian.Gaussian.mul_one,
    normalize_constant_of_ne directionNonzero,
    shift_one_constant_of_ne directionNonzero]
  by_cases originZero : origin = 0
  · subst origin
    rw [normalize_constant_zero, zero_add_normalize,
      normalize_linear_of_leading_ne_zero directionNonzero,
      add_constant_zero,
      normalize_linear_of_leading_ne_zero directionNonzero]
  · rw [normalize_constant_of_ne originZero,
      constant_add_linear origin directionNonzero,
      add_constant_zero,
      normalize_linear_of_leading_ne_zero directionNonzero]

private theorem coordinate_horizontal_real (y a b : Coordinate) :
    (horizontalEdge coordinatePolynomial y a b).realPart =
      coordinateVariable := by
  change realPart (composeLine coordinatePolynomial
      (horizontalBase y) horizontalDirection) = coordinateVariable
  rw [composeLine_coordinate (horizontalBase y) horizontalDirection (by
    intro equal
    have real := congrArg (fun z : Gaussian => z.re) equal
    change (1 : Coordinate) = 0 at real
    exact (Ne.symm RFAP.ConstructiveFraction.zero_ne_one) real)]
  rfl

private theorem coordinate_horizontal_imag (y a b : Coordinate) :
    (horizontalEdge coordinatePolynomial y a b).imagPart =
      rawLinearConstant y := by
  change imagPart (composeLine coordinatePolynomial
      (horizontalBase y) horizontalDirection) = rawLinearConstant y
  rw [composeLine_coordinate (horizontalBase y) horizontalDirection (by
    intro equal
    have real := congrArg (fun z : Gaussian => z.re) equal
    change (1 : Coordinate) = 0 at real
    exact (Ne.symm RFAP.ConstructiveFraction.zero_ne_one) real)]
  rfl

private theorem coordinate_vertical_real (x a b : Coordinate) :
    (verticalEdge coordinatePolynomial x a b).realPart =
      rawLinearConstant x := by
  change realPart (composeLine coordinatePolynomial
      (verticalBase x) verticalDirection) = rawLinearConstant x
  rw [composeLine_coordinate (verticalBase x) verticalDirection (by
    intro equal
    have imaginary := congrArg (fun z : Gaussian => z.im) equal
    change (1 : Coordinate) = 0 at imaginary
    exact (Ne.symm RFAP.ConstructiveFraction.zero_ne_one) imaginary)]
  rfl

private theorem coordinate_vertical_imag (x a b : Coordinate) :
    (verticalEdge coordinatePolynomial x a b).imagPart =
      coordinateVariable := by
  change imagPart (composeLine coordinatePolynomial
      (verticalBase x) verticalDirection) = coordinateVariable
  rw [composeLine_coordinate (verticalBase x) verticalDirection (by
    intro equal
    have imaginary := congrArg (fun z : Gaussian => z.im) equal
    change (1 : Coordinate) = 0 at imaginary
    exact (Ne.symm RFAP.ConstructiveFraction.zero_ne_one) imaginary)]
  rfl

@[simp] private theorem rawLinearConstant_eval (c t : Coordinate) :
    (rawLinearConstant c).eval t = c := by
  simp [rawLinearConstant, eval, evalCoeffs]

theorem rawLinearConstant_isZero_false {c : Coordinate}
    (nonzero : c ≠ 0) : (rawLinearConstant c).isZero = false := by
  simp [rawLinearConstant, isZero, normalize, nonzero]

theorem rawLinearConstant_degreeCount {c : Coordinate}
    (nonzero : c ≠ 0) : (rawLinearConstant c).degreeCount = 1 := by
  simp [degreeCount, rawLinearConstant, normalize, nonzero]

theorem rawLinearConstant_natDegree {c : Coordinate}
    (nonzero : c ≠ 0) : (rawLinearConstant c).natDegree = 0 := by
  simp [natDegree, rawLinearConstant_degreeCount nonzero]

theorem rawLinearConstant_normalize {c : Coordinate}
    (nonzero : c ≠ 0) :
    (rawLinearConstant c).normalize = constant c := by
  apply RFAP.ComputablePolynomial.DensePolynomial.ext
  simp [rawLinearConstant, normalize, constant, nonzero]

theorem coordinateVariable_isZero_false :
    coordinateVariable.isZero = false := by
  apply isZero_false_of_eval_ne (x := (1 : Coordinate))
  rw [coordinateVariable_eval]
  exact Ne.symm RFAP.ConstructiveFraction.zero_ne_one

theorem coordinateVariable_degreeCount :
    coordinateVariable.degreeCount = 2 := by
  rw [coordinateVariable, degreeCount,
    normalize_linear_of_leading_ne_zero
      (Ne.symm RFAP.ConstructiveFraction.zero_ne_one)]
  rfl

theorem coordinateVariable_natDegree :
    coordinateVariable.natDegree = 1 := by
  rw [natDegree, coordinateVariable_degreeCount]

private theorem signedChain_variable_rawLinearConstant
    {c : Coordinate} (nonzero : c ≠ 0) :
    signedRemainderChain coordinateVariable (rawLinearConstant c) =
      [coordinateVariable, rawLinearConstant c] :=
  signedRemainderChain_eq_pair_of_second_degreeCount_one
    (rawLinearConstant_isZero_false nonzero)
    (rawLinearConstant_degreeCount nonzero)

theorem signedChain_rawLinearConstant_variable
    {c : Coordinate} (nonzero : c ≠ 0) :
    signedRemainderChain (rawLinearConstant c) coordinateVariable =
      [rawLinearConstant c, coordinateVariable,
        -((rawLinearConstant c).normalize)] := by
  rw [signedRemainderChain_eq_cons_of_degree_lt
    (rawLinearConstant_isZero_false nonzero)
    coordinateVariable_isZero_false (by
      rw [rawLinearConstant_natDegree nonzero,
        coordinateVariable_natDegree]
      decide)]
  have negativeNonzero :
      (-((rawLinearConstant c).normalize)).isZero = false := by
    simpa only [isZero_neg, isZero_normalize] using
      rawLinearConstant_isZero_false nonzero
  have negativeCount :
      (-((rawLinearConstant c).normalize)).degreeCount = 1 := by
    simpa only [degreeCount_neg, degreeCount_normalize] using
      rawLinearConstant_degreeCount nonzero
  rw [signedRemainderChain_eq_pair_of_second_degreeCount_one
    negativeNonzero negativeCount]

theorem coordinate_bottom_winding {R : Coordinate} (positive : 0 < R) :
    (horizontalEdge coordinatePolynomial (-R) (-R) R).doubledWinding = 0 := by
  rw [PolynomialEdge.doubledWinding,
    coordinate_horizontal_real, coordinate_horizontal_imag]
  change cauchyIndex2 coordinateVariable (rawLinearConstant (-R)) (-R) R = 0
  have nonzero : -R ≠ 0 := by
    intro negativeZero
    have positiveZero := congrArg Neg.neg negativeZero
    simp only [_root_.neg_neg, neg_zero] at positiveZero
    exact positive.ne' positiveZero
  rw [cauchyIndex2,
    signedChain_rawLinearConstant_variable nonzero,
    rawLinearConstant_normalize nonzero]
  simp only [endpointVariation2, List.map_cons, List.map_nil,
    rawLinearConstant_eval, coordinateVariable_eval, eval_neg, eval_constant,
    variation2, _root_.neg_neg]
  rw [signJump_self, signJump_self]
  have opposite : (-R) * R < 0 := by
    rw [neg_mul]
    exact neg_neg_of_pos
      (RFAP.ConstructiveFraction.mul_pos_direct positive positive)
  rw [signJump_eq_two_of_mul_neg opposite]
  decide

theorem coordinate_top_winding {R : Coordinate} (positive : 0 < R) :
    (horizontalEdge coordinatePolynomial R R (-R)).doubledWinding = 0 := by
  rw [PolynomialEdge.doubledWinding,
    coordinate_horizontal_real, coordinate_horizontal_imag]
  change cauchyIndex2 coordinateVariable (rawLinearConstant R) R (-R) = 0
  have nonzero : R ≠ 0 := positive.ne'
  rw [cauchyIndex2,
    signedChain_rawLinearConstant_variable nonzero,
    rawLinearConstant_normalize nonzero]
  simp only [endpointVariation2, List.map_cons, List.map_nil,
    rawLinearConstant_eval, coordinateVariable_eval, eval_neg, eval_constant,
    variation2]
  rw [signJump_self, signJump_self]
  have opposite : R * (-R) < 0 := by
    rw [mul_neg]
    exact neg_neg_of_pos
      (RFAP.ConstructiveFraction.mul_pos_direct positive positive)
  rw [signJump_eq_two_of_mul_neg opposite]
  decide

theorem coordinate_right_winding {R : Coordinate} (positive : 0 < R) :
    (verticalEdge coordinatePolynomial R (-R) R).doubledWinding = 2 := by
  rw [PolynomialEdge.doubledWinding,
    coordinate_vertical_real, coordinate_vertical_imag]
  change cauchyIndex2 (rawLinearConstant R) coordinateVariable (-R) R = 2
  have nonzero : R ≠ 0 := positive.ne'
  rw [cauchyIndex2, signedChain_variable_rawLinearConstant nonzero]
  simp only [endpointVariation2, List.map_cons, List.map_nil,
    rawLinearConstant_eval, coordinateVariable_eval, variation2]
  rw [signJump_self]
  have opposite : (-R) * R < 0 := by
    rw [neg_mul]
    exact neg_neg_of_pos
      (RFAP.ConstructiveFraction.mul_pos_direct positive positive)
  rw [signJump_eq_two_of_mul_neg opposite]
  decide

theorem coordinate_left_winding {R : Coordinate} (positive : 0 < R) :
    (verticalEdge coordinatePolynomial (-R) R (-R)).doubledWinding = 2 := by
  rw [PolynomialEdge.doubledWinding,
    coordinate_vertical_real, coordinate_vertical_imag]
  change cauchyIndex2 (rawLinearConstant (-R)) coordinateVariable R (-R) = 2
  have nonzero : -R ≠ 0 := by
    intro negativeZero
    have positiveZero := congrArg Neg.neg negativeZero
    simp only [_root_.neg_neg, neg_zero] at positiveZero
    exact positive.ne' positiveZero
  rw [cauchyIndex2, signedChain_variable_rawLinearConstant nonzero]
  simp only [endpointVariation2, List.map_cons, List.map_nil,
    rawLinearConstant_eval, coordinateVariable_eval, variation2]
  rw [signJump_self]
  have opposite : R * (-R) < 0 := by
    rw [mul_neg]
    exact neg_neg_of_pos
      (RFAP.ConstructiveFraction.mul_pos_direct positive positive)
  rw [signJump_eq_two_of_mul_neg opposite]
  decide

/-- The coordinate polynomial has raw winding four, doubled winding two,
and ordinary winding one on every positive constructive symmetric square. -/
theorem coordinate_symmetric_normalization {R : Coordinate} (positive : 0 < R) :
    let box := RFAP.Boxes.Box.symmetric R positive.le
    quadrupledBoxWinding coordinatePolynomial box = 4 ∧
      doubledBoxWinding coordinatePolynomial box = 2 ∧
      boxWinding coordinatePolynomial box = 1 := by
  dsimp only
  have raw : quadrupledBoxWinding coordinatePolynomial
      (RFAP.Boxes.Box.symmetric R positive.le) = 4 := by
    rw [quadrupledBoxWinding_eq]
    dsimp only [RFAP.Boxes.Box.symmetric]
    rw [coordinate_bottom_winding positive,
      coordinate_right_winding positive,
      coordinate_top_winding positive,
      coordinate_left_winding positive]
    decide
  refine ⟨raw, ?_, ?_⟩
  · rw [doubledBoxWinding, raw]
    decide
  · rw [boxWinding, raw]
    decide

/-! ## Positive coordinate powers -/

/-- Finite multiplication program for `Z^(n+1)`, avoiding a zero-exponent
case in the positive-degree global theorem. -/
def coordinatePositivePower : Nat → GaussianPolynomial
  | 0 => coordinatePolynomial
  | n + 1 => coordinatePositivePower n * coordinatePolynomial

private theorem fold_coordinate_zeros (n : Nat) :
    (List.replicate n (0 : Gaussian)).foldl
      (fun value a => shift 1 value + scale a coordinatePolynomial)
      coordinatePolynomial =
        ⟨(1 : Gaussian) :: List.replicate (n + 1) 0⟩ := by
  induction n with
  | zero => rfl
  | succ n inductionHypothesis =>
      rw [List.replicate_succ', QuotientFreeList.foldl_append, inductionHypothesis]
      simp only [List.foldl_cons, List.foldl_nil, scale_zero_left,
        add_zero_normalize, normalize_shift]
      rw [shift, if_neg]
      · apply RFAP.ComputablePolynomial.DensePolynomial.ext
        simp only [normalize]
        rw [List.dropWhile_cons_of_neg (by simp)]
        simp only [List.replicate_succ', List.replicate_zero,
          List.nil_append, List.cons_append, List.append_assoc]
      · simp [isZero, normalize]

/-- Exact finite coefficient list of the positive coordinate power. -/
theorem coordinatePositivePower_coeffs (n : Nat) :
    (coordinatePositivePower n).coeffs =
      (1 : Gaussian) :: List.replicate (n + 1) 0 := by
  induction n with
  | zero => rfl
  | succ n inductionHypothesis =>
      rw [coordinatePositivePower]
      rw [show coordinatePositivePower n =
          ⟨(1 : Gaussian) :: List.replicate (n + 1) 0⟩ by
        apply RFAP.ComputablePolynomial.DensePolynomial.ext
        exact inductionHypothesis]
      change (List.foldl
        (fun value a => shift 1 value + scale a coordinatePolynomial)
        0 ((1 : Gaussian) :: List.replicate (n + 1) 0)).coeffs = _
      simp only [List.foldl_cons, shift_zero, scale_one_left,
        zero_add_normalize]
      exact congrArg (fun polynomial : GaussianPolynomial => polynomial.coeffs)
        (fold_coordinate_zeros (n + 1))

theorem coordinatePositivePower_eval (n : Nat) (z : Gaussian) :
    (coordinatePositivePower n).eval z = z ^ (n + 1) := by
  induction n with
  | zero =>
      rw [show coordinatePositivePower 0 = coordinatePolynomial by rfl,
        coordinatePolynomial_eval]
      simp
  | succ n inductionHypothesis =>
      rw [coordinatePositivePower, eval_mul, inductionHypothesis,
        coordinatePolynomial_eval]
      exact (pow_succ z (n + 1)).symm

private theorem coordinatePolynomial_isZero_false :
    coordinatePolynomial.isZero = false := by
  simp [coordinatePolynomial, isZero, normalize]

theorem coordinatePositivePower_isZero_false (n : Nat) :
    (coordinatePositivePower n).isZero = false := by
  induction n with
  | zero => exact coordinatePolynomial_isZero_false
  | succ n inductionHypothesis =>
      rw [coordinatePositivePower]
      exact isZero_mul_eq_false inductionHypothesis
        coordinatePolynomial_isZero_false

private theorem coordinatePolynomial_natDegree :
    coordinatePolynomial.natDegree = 1 := by
  simp [coordinatePolynomial, natDegree, degreeCount, normalize]

theorem coordinatePositivePower_natDegree (n : Nat) :
    (coordinatePositivePower n).natDegree = n + 1 := by
  induction n with
  | zero => exact coordinatePolynomial_natDegree
  | succ n inductionHypothesis =>
      rw [coordinatePositivePower,
        natDegree_mul (coordinatePositivePower_isZero_false n)
          coordinatePolynomial_isZero_false,
        inductionHypothesis, coordinatePolynomial_natDegree]

private theorem point_ne_zero_of_im_ne_zero (x y : Coordinate) (hy : y ≠ 0) :
    point x y ≠ 0 := by
  intro equal
  have imaginary := congrArg (fun z : Gaussian => z.im) equal
  exact hy imaginary

private theorem point_ne_zero_of_re_ne_zero (x y : Coordinate) (hx : x ≠ 0) :
    point x y ≠ 0 := by
  intro equal
  have real := congrArg (fun z : Gaussian => z.re) equal
  exact hx real

/-- Every positive coordinate power is pointwise nonzero on the boundary of
a positive symmetric constructive square. -/
theorem coordinatePositivePower_symmetric_boundaryCoprime
    {R : Coordinate} (positive : 0 < R) (n : Nat) :
    BoundaryCoprime (coordinatePositivePower n)
      (RFAP.Boxes.Box.symmetric R positive.le) := by
  have rNonzero : R ≠ 0 := positive.ne'
  have negativeRNonzero : -R ≠ 0 := by
    intro negativeZero
    have positiveZero := congrArg Neg.neg negativeZero
    simp only [_root_.neg_neg, neg_zero] at positiveZero
    exact rNonzero positiveZero
  constructor
  · change (PolynomialEdge.ofLine (coordinatePositivePower n)
      (horizontalBase (-R)) horizontalDirection (-R) R).Coprime
    apply PolynomialEdge.ofLine_coprime_of_eval_ne_zero
    intro t
    rw [line_horizontal, coordinatePositivePower_eval]
    exact pow_ne_zero_direct _
      (point_ne_zero_of_im_ne_zero t (-R) negativeRNonzero) _
  · change (PolynomialEdge.ofLine (coordinatePositivePower n)
      (verticalBase R) verticalDirection (-R) R).Coprime
    apply PolynomialEdge.ofLine_coprime_of_eval_ne_zero
    intro t
    rw [line_vertical, coordinatePositivePower_eval]
    exact pow_ne_zero_direct _
      (point_ne_zero_of_re_ne_zero R t rNonzero) _
  · change (PolynomialEdge.ofLine (coordinatePositivePower n)
      (horizontalBase R) horizontalDirection R (-R)).Coprime
    apply PolynomialEdge.ofLine_coprime_of_eval_ne_zero
    intro t
    rw [line_horizontal, coordinatePositivePower_eval]
    exact pow_ne_zero_direct _
      (point_ne_zero_of_im_ne_zero t R rNonzero) _
  · change (PolynomialEdge.ofLine (coordinatePositivePower n)
      (verticalBase (-R)) verticalDirection R (-R)).Coprime
    apply PolynomialEdge.ofLine_coprime_of_eval_ne_zero
    intro t
    rw [line_vertical, coordinatePositivePower_eval]
    exact pow_ne_zero_direct _
      (point_ne_zero_of_re_ne_zero (-R) t negativeRNonzero) _

/-- The coordinate itself has the explicit radial squared-norm clearance on
the boundary of a symmetric square. -/
def coordinate_symmetric_boundaryClearance
    {R : Coordinate} (positive : 0 < R) :
    RFAP.BoxClearance.BoundaryClearance coordinatePolynomial
      (RFAP.Boxes.Box.symmetric R positive.le) where
  bound := R ^ 2
  positive := by
    rw [pow_two]
    exact RFAP.ConstructiveFraction.mul_pos_direct positive positive
  lower := by
    intro z boundary
    rw [coordinatePolynomial_eval]
    rcases boundary with ⟨_inside, side⟩
    rcases side with left | right | bottom | top
    · change z.re = -R at left
      change R ^ 2 ≤ z.re ^ 2 + z.im ^ 2
      rw [left]
      rw [show (-R) ^ 2 = R ^ 2 by ring1]
      exact le_add_of_nonneg_right
        (RFAP.ConstructiveFraction.sq_nonneg_direct z.im)
    · change z.re = R at right
      change R ^ 2 ≤ z.re ^ 2 + z.im ^ 2
      rw [right]
      exact le_add_of_nonneg_right
        (RFAP.ConstructiveFraction.sq_nonneg_direct z.im)
    · change z.im = -R at bottom
      change R ^ 2 ≤ z.re ^ 2 + z.im ^ 2
      rw [bottom]
      rw [show (-R) ^ 2 = R ^ 2 by ring1]
      exact le_add_of_nonneg_left
        (RFAP.ConstructiveFraction.sq_nonneg_direct z.re)
    · change z.im = R at top
      change R ^ 2 ≤ z.re ^ 2 + z.im ^ 2
      rw [top]
      exact le_add_of_nonneg_left
        (RFAP.ConstructiveFraction.sq_nonneg_direct z.re)

/-- Every positive coordinate power carries an explicit product clearance on
a positive symmetric square. -/
def coordinatePositivePower_symmetric_boundaryClearance
    {R : Coordinate} (positive : 0 < R) :
    ∀ n : Nat,
      RFAP.BoxClearance.BoundaryClearance
        (coordinatePositivePower n)
        (RFAP.Boxes.Box.symmetric R positive.le)
  | 0 => coordinate_symmetric_boundaryClearance positive
  | n + 1 =>
      RFAP.BoxClearance.BoundaryClearance.mul
        (coordinatePositivePower_symmetric_boundaryClearance positive n)
        (coordinate_symmetric_boundaryClearance positive)

/-- Raw winding of the positive coordinate powers follows by the audited
closed-box product theorem. -/
theorem quadrupledBoxWinding_coordinatePositivePower
    {R : Coordinate} (positive : 0 < R) (n : Nat) :
    quadrupledBoxWinding (coordinatePositivePower n)
        (RFAP.Boxes.Box.symmetric R positive.le) =
      (4 : Int) * (n + 1) := by
  induction n with
  | zero =>
      change quadrupledBoxWinding coordinatePolynomial
          (RFAP.Boxes.Box.symmetric R positive.le) = 4
      exact (coordinate_symmetric_normalization positive).1
  | succ n inductionHypothesis =>
      let box := RFAP.Boxes.Box.symmetric R positive.le
      have proper : box.Proper := by
        constructor <;> exact (neg_lt_zero.mpr positive).trans positive
      have product :=
        RFAP.WindingProduct.quadrupledBoxWinding_mul_of_boundaryClearances
          (coordinatePositivePower n) coordinatePolynomial box proper
          (coordinatePositivePower_symmetric_boundaryClearance positive n)
          (coordinate_symmetric_boundaryClearance positive)
      have coordinateWinding := (coordinate_symmetric_normalization positive).1
      change quadrupledBoxWinding
          (coordinatePositivePower n * coordinatePolynomial) box =
        (4 : Int) * (n + 2)
      rw [product, inductionHypothesis, coordinateWinding]
      ring1

/-! ## Coefficient-computed large square -/

/-- Finite weighted sum of squared coefficient norms, with the displayed
natural exponent as the first weight. -/
def weightedNormSum : List Gaussian → Nat → Coordinate
  | [], _ => 0
  | coefficient :: coefficients, exponent =>
      normSq coefficient * (2 : Coordinate) ^ exponent +
        weightedNormSum coefficients (exponent + 1)

theorem weightedNormSum_nonneg (coefficients : List Gaussian) (exponent : Nat) :
    0 ≤ weightedNormSum coefficients exponent := by
  induction coefficients generalizing exponent with
  | nil => exact le_rfl
  | cons coefficient coefficients inductionHypothesis =>
      exact add_nonneg
        (RFAP.ConstructiveFraction.mul_nonneg_direct
          (normSq_nonneg coefficient)
          (RFAP.ConstructiveFraction.pow_nonneg_direct
            (by decide : (0 : Coordinate) ≤ 2) exponent))
        (inductionHypothesis (exponent + 1))

theorem weightedNormSum_append (left right : List Gaussian)
    (exponent : Nat) :
    weightedNormSum (left ++ right) exponent =
      weightedNormSum left exponent +
        weightedNormSum right (exponent + left.length) := by
  induction left generalizing exponent with
  | nil =>
      simp [weightedNormSum]
  | cons coefficient coefficients inductionHypothesis =>
      rw [List.cons_append, weightedNormSum, weightedNormSum,
        inductionHypothesis]
      simp only [List.length_cons]
      have exponentIdentity :
          exponent + 1 + coefficients.length =
            exponent + (coefficients.length + 1) := by ring1
      rw [exponentIdentity]
      ring1

theorem weightedNormSum_reverse_cons
    (coefficient : Gaussian) (coefficients : List Gaussian) :
    weightedNormSum ((coefficient :: coefficients).reverse) 0 =
      weightedNormSum coefficients.reverse 0 +
        normSq coefficient * (2 : Coordinate) ^ coefficients.length := by
  rw [List.reverse_cons, weightedNormSum_append]
  simp only [List.length_reverse, Nat.zero_add, weightedNormSum]
  ring1

/-- The monomial squared-norm sum is bounded by the explicit reversed
coefficient weight and the largest displayed radial power. -/
theorem monomialNormSqSum_le_weighted :
    ∀ (coefficients : List Gaussian) (radiusSq radialSq : Coordinate),
      coefficients ≠ [] → 0 ≤ radiusSq →
      radiusSq ≤ 2 * radialSq → 1 ≤ radialSq →
      RFAP.ConstructiveFiniteNorm.monomialNormSqSum coefficients radiusSq ≤
        weightedNormSum coefficients.reverse 0 *
          radialSq ^ (coefficients.length - 1)
  | [], _, _, nonempty, _, _, _ => (nonempty rfl).elim
  | coefficient :: coefficients, radiusSq, radialSq,
      _, radiusNonnegative, radiusBound, oneLeRadial => by
      cases coefficients with
      | nil =>
          simp [RFAP.ConstructiveFiniteNorm.monomialNormSqSum,
            weightedNormSum]
      | cons next remaining =>
          let tail := next :: remaining
          have tailNonempty : tail ≠ [] := by simp [tail]
          have tailBound := monomialNormSqSum_le_weighted tail radiusSq
            radialSq tailNonempty radiusNonnegative radiusBound oneLeRadial
          have powerBound := RFAP.ConstructiveFraction.pow_le_pow_direct
            radiusNonnegative radiusBound tail.length
          have firstBound :
              normSq coefficient * radiusSq ^ tail.length ≤
                normSq coefficient * (2 * radialSq) ^ tail.length :=
            RFAP.ConstructiveFraction.mul_le_mul_of_nonneg_left_direct
              powerBound (normSq_nonneg coefficient)
          have radialNonnegative : 0 ≤ radialSq :=
            (by decide : (0 : Coordinate) ≤ 1).trans oneLeRadial
          have radialPowerLift :
              radialSq ^ remaining.length ≤
                radialSq ^ (remaining.length + 1) := by
            calc
              radialSq ^ remaining.length =
                  radialSq ^ remaining.length * 1 := by ring1
              _ ≤ radialSq ^ remaining.length * radialSq :=
                RFAP.ConstructiveFraction.mul_le_mul_of_nonneg_left_direct
                  oneLeRadial
                  (RFAP.ConstructiveFraction.pow_nonneg_direct
                    radialNonnegative remaining.length)
              _ = radialSq ^ (remaining.length + 1) := by rw [pow_succ]
          have weightedLift :
              weightedNormSum tail.reverse 0 *
                  radialSq ^ remaining.length ≤
                weightedNormSum tail.reverse 0 *
                  radialSq ^ (remaining.length + 1) :=
            RFAP.ConstructiveFraction.mul_le_mul_of_nonneg_left_direct
              radialPowerLift (weightedNormSum_nonneg tail.reverse 0)
          have tailLift :
              RFAP.ConstructiveFiniteNorm.monomialNormSqSum tail radiusSq ≤
                weightedNormSum tail.reverse 0 *
                  radialSq ^ tail.length := by
            exact tailBound.trans (by
              simpa only [tail, List.length_cons, Nat.add_sub_cancel]
                using weightedLift)
          rw [RFAP.ConstructiveFiniteNorm.monomialNormSqSum]
          rw [weightedNormSum_reverse_cons]
          simp only [List.length_cons]
          calc
            normSq coefficient * radiusSq ^ (remaining.length + 1) +
                  RFAP.ConstructiveFiniteNorm.monomialNormSqSum tail radiusSq ≤
                normSq coefficient * (2 * radialSq) ^
                    (remaining.length + 1) +
                  weightedNormSum tail.reverse 0 *
                    radialSq ^ (remaining.length + 1) :=
              add_le_add firstBound tailLift
            _ = (weightedNormSum tail.reverse 0 +
                  normSq coefficient * (2 : Coordinate) ^
                    (remaining.length + 1)) *
                radialSq ^ (remaining.length + 1) := by
              rw [mul_pow]
              ring1

/-- Normalized finite coefficient tail, containing exactly the slots below
the displayed leading term. -/
def lowerCoefficients (p : GaussianPolynomial) : List Gaussian :=
  p.normalize.coeffs.tail

theorem lowerCoefficients_length {p : GaussianPolynomial}
    (nonzero : p.isZero = false) :
    (lowerCoefficients p).length = p.natDegree := by
  obtain ⟨tail, coefficients, length⟩ := normalized_coeffs_shape nonzero
  unfold lowerCoefficients
  rw [coefficients]
  exact length

/-- Coefficient weight for all slots below the normalized leading degree. -/
def denseLowerCoefficientWeight (p : GaussianPolynomial) : Coordinate :=
  (p.natDegree : Coordinate) *
    weightedNormSum (lowerCoefficients p).reverse 0

theorem denseLowerCoefficientWeight_nonneg (p : GaussianPolynomial) :
    0 ≤ denseLowerCoefficientWeight p := by
  exact RFAP.ConstructiveFraction.mul_nonneg_direct
    (RFAP.ConstructiveFraction.natCast_le_direct (Nat.zero_le p.natDegree))
    (weightedNormSum_nonneg _ 0)

/-- Explicit finite coefficient-derived radius used by the constructive
global winding theorem. -/
def denseLargeSquareRadius (p : GaussianPolynomial) : Coordinate :=
  max 1 (denseLowerCoefficientWeight p / normSq p.leadingCoeff + 1)

theorem one_le_denseLargeSquareRadius (p : GaussianPolynomial) :
    1 ≤ denseLargeSquareRadius p :=
  le_max_left _ _

theorem denseLargeSquareRadius_pos (p : GaussianPolynomial) :
    0 < denseLargeSquareRadius p :=
  (by decide : (0 : Coordinate) < 1).trans_le
    (one_le_denseLargeSquareRadius p)

def largeSquareBox (p : GaussianPolynomial) : Box :=
  RFAP.Boxes.Box.symmetric (denseLargeSquareRadius p)
    (denseLargeSquareRadius_pos p).le

theorem isZero_false_of_natDegree_pos {p : GaussianPolynomial}
    (degreePositive : 0 < p.natDegree) : p.isZero = false := by
  cases zero : p.isZero with
  | false => rfl
  | true =>
      have count := degreeCount_eq_zero_of_isZero zero
      have degreeZero : p.natDegree = 0 := by
        rw [natDegree, count]
      rw [degreeZero] at degreePositive
      exact (Nat.not_lt_zero 0 degreePositive).elim

theorem largeSquareBox_proper (p : GaussianPolynomial) :
    (largeSquareBox p).Proper := by
  have positive := denseLargeSquareRadius_pos p
  constructor <;>
    exact (neg_lt_zero.mpr positive).trans positive

/-! ## Constants and the leading monomial -/

def gaussianConstant (c : Gaussian) : GaussianPolynomial := constant c

@[simp] theorem gaussianConstant_eval (c z : Gaussian) :
    (gaussianConstant c).eval z = c := by
  simp [gaussianConstant]

theorem gaussianConstant_boundaryCoprime {c : Gaussian} (nonzero : c ≠ 0)
    (box : Box) : BoundaryCoprime (gaussianConstant c) box := by
  constructor
  · change (PolynomialEdge.ofLine (gaussianConstant c)
      (horizontalBase box.yLower) horizontalDirection
      box.xLower box.xUpper).Coprime
    apply PolynomialEdge.ofLine_coprime_of_eval_ne_zero
    intro t
    rw [gaussianConstant_eval]
    exact nonzero
  · change (PolynomialEdge.ofLine (gaussianConstant c)
      (verticalBase box.xUpper) verticalDirection
      box.yLower box.yUpper).Coprime
    apply PolynomialEdge.ofLine_coprime_of_eval_ne_zero
    intro t
    rw [gaussianConstant_eval]
    exact nonzero
  · change (PolynomialEdge.ofLine (gaussianConstant c)
      (horizontalBase box.yUpper) horizontalDirection
      box.xUpper box.xLower).Coprime
    apply PolynomialEdge.ofLine_coprime_of_eval_ne_zero
    intro t
    rw [gaussianConstant_eval]
    exact nonzero
  · change (PolynomialEdge.ofLine (gaussianConstant c)
      (verticalBase box.xLower) verticalDirection
      box.yUpper box.yLower).Coprime
    apply PolynomialEdge.ofLine_coprime_of_eval_ne_zero
    intro t
    rw [gaussianConstant_eval]
    exact nonzero

/-- A nonzero constant polynomial carries its exact norm as a quantitative
boundary clearance on every box. -/
def gaussianConstant_boundaryClearance
    {c : Gaussian} (nonzero : c ≠ 0) (box : Box) :
    RFAP.BoxClearance.BoundaryClearance
      (gaussianConstant c) box where
  bound := normSq c
  positive := normSq_pos nonzero
  lower := by
    intro z _boundary
    rw [gaussianConstant_eval]

private theorem composeLine_gaussianConstant_of_ne
    (c origin direction : Gaussian) (nonzero : c ≠ 0) :
    composeLine (gaussianConstant c) origin direction = constant c := by
  rw [composeLine, composeLineCoeffs]
  simp only [gaussianConstant, constant_coeffs, List.foldl_cons,
    List.foldl_nil]
  rw [mulLine_zero, zero_add_normalize, normalize_constant_of_ne nonzero]

private theorem gaussianConstant_pathReal
    (c origin direction : Gaussian) (nonzero : c ≠ 0) :
    pathReal (gaussianConstant c) origin direction = constant c.re := by
  rw [pathReal, composeLine_gaussianConstant_of_ne c origin direction nonzero]
  rfl

private theorem gaussianConstant_pathImag
    (c origin direction : Gaussian) (nonzero : c ≠ 0) :
    pathImag (gaussianConstant c) origin direction = constant c.im := by
  rw [pathImag, composeLine_gaussianConstant_of_ne c origin direction nonzero]
  rfl

private theorem gaussianConstant_edge_winding
    (c origin direction : Gaussian) (a b : Coordinate) (nonzero : c ≠ 0) :
    (PolynomialEdge.ofLine (gaussianConstant c) origin direction a b).doubledWinding =
      cauchyIndex2 (constant c.re) (constant c.im) a b := by
  rw [PolynomialEdge.doubledWinding]
  change cauchyIndex2
      (pathReal (gaussianConstant c) origin direction)
      (pathImag (gaussianConstant c) origin direction) a b = _
  rw [gaussianConstant_pathReal c origin direction nonzero,
    gaussianConstant_pathImag c origin direction nonzero]

/-- Every affine traversal of a nonzero constant Gaussian polynomial has
zero Cauchy index. -/
theorem gaussianConstant_edge_winding_zero
    {c : Gaussian} (nonzero : c ≠ 0)
    (origin direction : Gaussian) (a b : Coordinate) :
    (PolynomialEdge.ofLine (gaussianConstant c) origin direction a b).doubledWinding =
      0 := by
  rw [gaussianConstant_edge_winding c origin direction a b nonzero]
  by_cases realZero : c.re = 0
  · have secondZero : (constant c.re).isZero = true := by
      simp [realZero, isZero, normalize]
    unfold cauchyIndex2
    rw [signedRemainderChain, signedRemainderChainWF_eq]
    simp only [secondZero, ↓reduceIte, endpointVariation2,
      List.map_cons, List.map_nil, eval_constant]
    exact Int.sub_self _
  · have secondNonzero : (constant c.re).isZero = false := by
      simp [isZero, normalize, realZero]
    have secondCount : (constant c.re).degreeCount = 1 := by
      have positive := degreeCount_pos_of_isZero_false secondNonzero
      have atMostOne := degreeCount_constant_le_one c.re
      omega
    rw [cauchyIndex2,
      signedRemainderChain_eq_pair_of_second_degreeCount_one
        secondNonzero secondCount]
    simp only [endpointVariation2, List.map_cons, List.map_nil,
      eval_constant]
    exact Int.sub_self _

/-- A nonzero constant path has zero raw winding on every constructive box.
Oppositely oriented edges cancel exactly; no product formula is used. -/
theorem quadrupledBoxWinding_gaussianConstant
    {c : Gaussian} (nonzero : c ≠ 0) (box : Box) :
    quadrupledBoxWinding (gaussianConstant c) box = 0 := by
  rw [quadrupledBoxWinding_eq]
  change
    (PolynomialEdge.ofLine (gaussianConstant c)
        (horizontalBase box.yLower) horizontalDirection
        box.xLower box.xUpper).doubledWinding +
      (PolynomialEdge.ofLine (gaussianConstant c)
        (verticalBase box.xUpper) verticalDirection
        box.yLower box.yUpper).doubledWinding +
      (PolynomialEdge.ofLine (gaussianConstant c)
        (horizontalBase box.yUpper) horizontalDirection
        box.xUpper box.xLower).doubledWinding +
      (PolynomialEdge.ofLine (gaussianConstant c)
        (verticalBase box.xLower) verticalDirection
        box.yUpper box.yLower).doubledWinding = 0
  rw [gaussianConstant_edge_winding _ _ _ _ _ nonzero,
    gaussianConstant_edge_winding _ _ _ _ _ nonzero,
    gaussianConstant_edge_winding _ _ _ _ _ nonzero,
    gaussianConstant_edge_winding _ _ _ _ _ nonzero,
    cauchyIndex2_reverse (constant c.re) (constant c.im)
      box.xLower box.xUpper,
    cauchyIndex2_reverse (constant c.re) (constant c.im)
      box.yLower box.yUpper]
  ring1

/-- Executable leading monomial `a_d Z^d` for positive dense degree. -/
def leadingMonomial (p : GaussianPolynomial) : GaussianPolynomial :=
  gaussianConstant p.leadingCoeff *
    coordinatePositivePower (p.natDegree - 1)

/-- Exact finite coefficient list of the displayed leading monomial. -/
theorem leadingMonomial_coeffs {p : GaussianPolynomial}
    (degreePositive : 0 < p.natDegree) :
    (leadingMonomial p).coeffs =
      p.leadingCoeff :: List.replicate p.natDegree 0 := by
  have polynomialNonzero := isZero_false_of_natDegree_pos degreePositive
  have leadingNonzero := leadingCoeff_ne_zero polynomialNonzero
  unfold leadingMonomial gaussianConstant
  change (List.foldl
    (fun value a => shift 1 value + scale a
      (coordinatePositivePower (p.natDegree - 1)))
    0 [p.leadingCoeff]).coeffs = _
  simp only [List.foldl_cons, List.foldl_nil, shift_zero,
    zero_add_normalize, normalize_scale]
  rw [scale_coeffs_of_ne_zero leadingNonzero]
  have coordinateNormalized :
      (coordinatePositivePower (p.natDegree - 1)).normalize =
        coordinatePositivePower (p.natDegree - 1) := by
    apply RFAP.ComputablePolynomial.DensePolynomial.ext
    change ((coordinatePositivePower (p.natDegree - 1)).coeffs.dropWhile
      (· = 0)) = (coordinatePositivePower (p.natDegree - 1)).coeffs
    rw [coordinatePositivePower_coeffs,
      List.dropWhile_cons_of_neg (by simp)]
  rw [coordinateNormalized, coordinatePositivePower_coeffs]
  simp only [List.map_cons, List.map_replicate,
    RFAP.ConstructiveGaussian.Gaussian.mul_one,
    RFAP.ConstructiveGaussian.Gaussian.mul_zero]
  rw [Nat.sub_add_cancel (Nat.one_le_iff_ne_zero.mpr (by omega))]

theorem leadingMonomial_eval {p : GaussianPolynomial}
    (degreePositive : 0 < p.natDegree) (z : Gaussian) :
    (leadingMonomial p).eval z =
      p.leadingCoeff * z ^ p.natDegree := by
  rw [leadingMonomial, eval_mul, gaussianConstant_eval,
    coordinatePositivePower_eval]
  have exponent : p.natDegree - 1 + 1 = p.natDegree := by omega
  rw [exponent]

/-- The displayed leading coefficient clearance and the radial power
clearance multiply to a quantitative boundary certificate for the leading
monomial. -/
def leadingMonomial_largeSquare_boundaryClearance
    {p : GaussianPolynomial} (degreePositive : 0 < p.natDegree) :
    RFAP.BoxClearance.BoundaryClearance
      (leadingMonomial p) (largeSquareBox p) := by
  have polynomialNonzero := isZero_false_of_natDegree_pos degreePositive
  have leadingNonzero := leadingCoeff_ne_zero polynomialNonzero
  exact RFAP.BoxClearance.BoundaryClearance.mul
    (gaussianConstant_boundaryClearance leadingNonzero (largeSquareBox p))
    (by
      simpa only [largeSquareBox] using
        coordinatePositivePower_symmetric_boundaryClearance
          (denseLargeSquareRadius_pos p) (p.natDegree - 1))

/-- The leading monomial has raw winding four times the positive dense
degree on the coefficient-computed square. -/
theorem quadrupledBoxWinding_leadingMonomial
    {p : GaussianPolynomial} (degreePositive : 0 < p.natDegree) :
    quadrupledBoxWinding (leadingMonomial p) (largeSquareBox p) =
      (4 : Int) * p.natDegree := by
  have polynomialNonzero := isZero_false_of_natDegree_pos degreePositive
  have leadingNonzero := leadingCoeff_ne_zero polynomialNonzero
  have product :=
    RFAP.WindingProduct.quadrupledBoxWinding_mul_of_boundaryClearances
      (gaussianConstant p.leadingCoeff)
      (coordinatePositivePower (p.natDegree - 1))
      (largeSquareBox p) (largeSquareBox_proper p)
      (gaussianConstant_boundaryClearance leadingNonzero (largeSquareBox p))
      (by
        simpa only [largeSquareBox] using
          coordinatePositivePower_symmetric_boundaryClearance
            (denseLargeSquareRadius_pos p) (p.natDegree - 1))
  have powerWinding := quadrupledBoxWinding_coordinatePositivePower
    (denseLargeSquareRadius_pos p) (p.natDegree - 1)
  change quadrupledBoxWinding
      (gaussianConstant p.leadingCoeff *
        coordinatePositivePower (p.natDegree - 1))
      (largeSquareBox p) = (4 : Int) * p.natDegree
  rw [product,
    quadrupledBoxWinding_gaussianConstant leadingNonzero (largeSquareBox p)]
  rw [show quadrupledBoxWinding
      (coordinatePositivePower (p.natDegree - 1)) (largeSquareBox p) =
        (4 : Int) * (((p.natDegree - 1 : Nat) : Int) + 1) by
      simpa only [largeSquareBox] using powerWinding]
  omega

/-- Both normalized winding conventions inherit the exact leading-monomial
degree. -/
theorem leadingMonomial_largeSquare_normalization
    {p : GaussianPolynomial} (degreePositive : 0 < p.natDegree) :
    doubledBoxWinding (leadingMonomial p) (largeSquareBox p) =
        (2 : Int) * p.natDegree ∧
      boxWinding (leadingMonomial p) (largeSquareBox p) = p.natDegree := by
  have raw := quadrupledBoxWinding_leadingMonomial degreePositive
  constructor
  · rw [doubledBoxWinding, raw]
    omega
  · rw [boxWinding, raw]
    omega

/-- Executable polynomial consisting of exactly the normalized coefficient
slots below the leading term. -/
def lowerTermsPolynomial (p : GaussianPolynomial) : GaussianPolynomial :=
  ⟨lowerCoefficients p⟩

/-- Exact finite Horner split into the leading monomial and normalized lower
coefficient tail. -/
theorem leadingMonomial_add_lowerTerms_eval
    {p : GaussianPolynomial} (degreePositive : 0 < p.natDegree)
    (z : Gaussian) :
    (leadingMonomial p).eval z + (lowerTermsPolynomial p).eval z =
      p.eval z := by
  have polynomialNonzero := isZero_false_of_natDegree_pos degreePositive
  obtain ⟨tail, coefficients, tailLength⟩ :=
    normalized_coeffs_shape polynomialNonzero
  rw [leadingMonomial_eval degreePositive]
  change p.leadingCoeff * z ^ p.natDegree +
      evalCoeffs z (lowerCoefficients p) = p.eval z
  rw [← eval_normalize p z]
  change _ = evalCoeffs z p.normalize.coeffs
  rw [coefficients, evalCoeffs_cons_expansion]
  unfold lowerCoefficients
  rw [coefficients]
  simp only [List.tail_cons]
  rw [tailLength]

/-- The leading/lower split is an exact equality of finite normalized
coefficient lists.  This is stronger than evaluation equality and uses no
polynomial extensionality over a field. -/
theorem leadingMonomial_add_lowerTerms_eq_normalize
    {p : GaussianPolynomial} (degreePositive : 0 < p.natDegree) :
    leadingMonomial p + lowerTermsPolynomial p = p.normalize := by
  have polynomialNonzero := isZero_false_of_natDegree_pos degreePositive
  have leadingNonzero := leadingCoeff_ne_zero polynomialNonzero
  obtain ⟨tail, coefficients, tailLength⟩ :=
    normalized_coeffs_shape polynomialNonzero
  apply RFAP.ComputablePolynomial.DensePolynomial.ext
  have leadingEquality : leadingMonomial p =
      ⟨p.leadingCoeff :: List.replicate p.natDegree 0⟩ := by
    apply RFAP.ComputablePolynomial.DensePolynomial.ext
    exact leadingMonomial_coeffs degreePositive
  rw [leadingEquality]
  change (add ⟨p.leadingCoeff :: List.replicate p.natDegree 0⟩
    ⟨lowerCoefficients p⟩).coeffs = p.normalize.coeffs
  unfold lowerCoefficients
  rw [coefficients]
  simp only [List.tail_cons]
  simp [add, padLeft, normalize, tailLength, leadingNonzero]
  rw [← tailLength]
  exact zipWith_replicate_zero_add tail

/-- Cauchy--Schwarz bound for the normalized lower coefficient tail at a
point with a displayed squared-radius upper bound. -/
theorem normSq_lowerTermsPolynomial_eval_le
    {p : GaussianPolynomial} (degreePositive : 0 < p.natDegree)
    {z : Gaussian} {radialSq : Coordinate}
    (normUpper : normSq z ≤ 2 * radialSq) (oneLeRadial : 1 ≤ radialSq) :
    normSq ((lowerTermsPolynomial p).eval z) ≤
      denseLowerCoefficientWeight p *
        radialSq ^ (p.natDegree - 1) := by
  have polynomialNonzero := isZero_false_of_natDegree_pos degreePositive
  have coefficientLength := lowerCoefficients_length polynomialNonzero
  have coefficientsNonempty : lowerCoefficients p ≠ [] := by
    intro empty
    rw [empty] at coefficientLength
    simp only [List.length_nil] at coefficientLength
    omega
  have cauchy := RFAP.ConstructiveFiniteNorm.normSq_evalCoeffs_le
    (lowerCoefficients p) z
  have monomialBound := monomialNormSqSum_le_weighted
    (lowerCoefficients p) (normSq z) radialSq coefficientsNonempty
    (normSq_nonneg z) normUpper oneLeRadial
  have scaledMonomial :=
    RFAP.ConstructiveFraction.mul_le_mul_of_nonneg_left_direct
      monomialBound
      (RFAP.ConstructiveFraction.natCast_le_direct
        (Nat.zero_le (lowerCoefficients p).length))
  change normSq (evalCoeffs z (lowerCoefficients p)) ≤ _
  calc
    normSq (evalCoeffs z (lowerCoefficients p)) ≤
        ((lowerCoefficients p).length : Coordinate) *
          RFAP.ConstructiveFiniteNorm.monomialNormSqSum
            (lowerCoefficients p) (normSq z) := cauchy
    _ ≤ ((lowerCoefficients p).length : Coordinate) *
          (weightedNormSum (lowerCoefficients p).reverse 0 *
            radialSq ^ ((lowerCoefficients p).length - 1)) :=
      scaledMonomial
    _ = denseLowerCoefficientWeight p *
          radialSq ^ (p.natDegree - 1) := by
      rw [coefficientLength]
      unfold denseLowerCoefficientWeight
      ring1

theorem normSq_leadingMonomial_eval_lower
    {p : GaussianPolynomial} (degreePositive : 0 < p.natDegree)
    {z : Gaussian} {radialSq : Coordinate}
    (radialNonnegative : 0 ≤ radialSq)
    (normLower : radialSq ≤ normSq z) :
    normSq p.leadingCoeff * radialSq ^ p.natDegree ≤
      normSq ((leadingMonomial p).eval z) := by
  rw [leadingMonomial_eval degreePositive, normSq_mul, normSq_pow]
  exact RFAP.ConstructiveFraction.mul_le_mul_of_nonneg_left_direct
    (RFAP.ConstructiveFraction.pow_le_pow_direct
      radialNonnegative normLower p.natDegree)
    (normSq_nonneg p.leadingCoeff)

/-- The explicit coefficient weight is strictly smaller than the leading
coefficient norm times the squared computed radius. -/
theorem denseLowerCoefficientWeight_lt_leading_radiusSq
    {p : GaussianPolynomial} (degreePositive : 0 < p.natDegree) :
    denseLowerCoefficientWeight p <
      normSq p.leadingCoeff * denseLargeSquareRadius p ^ 2 := by
  have polynomialNonzero := isZero_false_of_natDegree_pos degreePositive
  have leadingNonzero := leadingCoeff_ne_zero polynomialNonzero
  have leadingPositive := normSq_pos leadingNonzero
  let weight := denseLowerCoefficientWeight p
  let leadingNorm := normSq p.leadingCoeff
  let radius := denseLargeSquareRadius p
  have strictStep : weight / leadingNorm < weight / leadingNorm + 1 := by
    have added := RFAP.ConstructiveFraction.add_lt_add_left_direct
      (by decide : (0 : Coordinate) < 1) (weight / leadingNorm)
    calc
      weight / leadingNorm = weight / leadingNorm + 0 := by ring1
      _ < weight / leadingNorm + 1 := added
  have quotientBelow : weight / leadingNorm < radius :=
    strictStep.trans_le (by
      dsimp only [radius, denseLargeSquareRadius]
      exact le_max_right _ _)
  have scaled := RFAP.ConstructiveFraction.mul_lt_mul_of_pos_right_direct
    quotientBelow leadingPositive
  have weightBelowLinear : weight < leadingNorm * radius := by
    change weight / leadingNorm * leadingNorm < radius * leadingNorm at scaled
    have cancel : weight / leadingNorm * leadingNorm = weight :=
      RFAP.ConstructiveFraction.div_mul_cancel_of_ne weight leadingNorm
        leadingPositive.ne'
    rw [cancel, RFAP.ConstructiveFraction.mul_comm radius leadingNorm] at scaled
    exact scaled
  have oneLeRadius : (1 : Coordinate) ≤ radius := by
    dsimp only [radius]
    exact one_le_denseLargeSquareRadius p
  have radiusNonnegative : 0 ≤ radius :=
    (by decide : (0 : Coordinate) ≤ 1).trans oneLeRadius
  have radiusLeSquare : radius ≤ radius ^ 2 := by
    rw [pow_two]
    calc
      radius = radius * 1 := by ring1
      _ ≤ radius * radius :=
        RFAP.ConstructiveFraction.mul_le_mul_of_nonneg_left_direct
          oneLeRadius radiusNonnegative
  have scaledRadius : leadingNorm * radius ≤ leadingNorm * radius ^ 2 :=
    RFAP.ConstructiveFraction.mul_le_mul_of_nonneg_left_direct radiusLeSquare
      (normSq_nonneg p.leadingCoeff)
  exact weightBelowLinear.trans_le scaledRadius

/-- Strict leading-term dominance at every point whose squared norm lies
between the displayed radial square and twice that square. -/
theorem largeSquare_radial_dominance
    {p : GaussianPolynomial} (degreePositive : 0 < p.natDegree)
    {z : Gaussian}
    (normLower : denseLargeSquareRadius p ^ 2 ≤ normSq z)
    (normUpper : normSq z ≤ 2 * denseLargeSquareRadius p ^ 2) :
    normSq ((lowerTermsPolynomial p).eval z) <
      normSq ((leadingMonomial p).eval z) := by
  let radiusSq := denseLargeSquareRadius p ^ 2
  have radiusPositive := denseLargeSquareRadius_pos p
  have radiusSqPositive : 0 < radiusSq :=
    by
      dsimp only [radiusSq]
      rw [pow_two]
      exact RFAP.ConstructiveFraction.mul_pos_direct
        radiusPositive radiusPositive
  have oneLeRadius := one_le_denseLargeSquareRadius p
  have oneLeRadiusSq : (1 : Coordinate) ≤ radiusSq := by
    dsimp only [radiusSq]
    rw [pow_two]
    calc
      1 = 1 * 1 := by ring1
      _ ≤ denseLargeSquareRadius p * denseLargeSquareRadius p :=
        RFAP.ConstructiveFraction.mul_le_mul_direct oneLeRadius oneLeRadius
          (by decide) radiusPositive.le
  have lowerBound := normSq_lowerTermsPolynomial_eval_le degreePositive
    (z := z) (radialSq := radiusSq) (by simpa only [radiusSq] using normUpper)
    oneLeRadiusSq
  have weightStrict := denseLowerCoefficientWeight_lt_leading_radiusSq
    degreePositive
  have powerPositive := RFAP.ConstructiveFraction.pow_pos_direct
    radiusSqPositive (p.natDegree - 1)
  have scaledStrict := RFAP.ConstructiveFraction.mul_lt_mul_of_pos_right_direct
    (by simpa only [radiusSq] using weightStrict) powerPositive
  have degreeIdentity : p.natDegree - 1 + 1 = p.natDegree := by omega
  have leadingRadial :
      normSq p.leadingCoeff * radiusSq ^ p.natDegree ≤
        normSq ((leadingMonomial p).eval z) :=
    normSq_leadingMonomial_eval_lower degreePositive radiusSqPositive.le
      (by simpa only [radiusSq] using normLower)
  calc
    normSq ((lowerTermsPolynomial p).eval z) ≤
        denseLowerCoefficientWeight p *
          radiusSq ^ (p.natDegree - 1) := lowerBound
    _ < (normSq p.leadingCoeff * radiusSq) *
          radiusSq ^ (p.natDegree - 1) := scaledStrict
    _ = normSq p.leadingCoeff *
          (radiusSq ^ (p.natDegree - 1) * radiusSq) := by ring1
    _ = normSq p.leadingCoeff *
          radiusSq ^ (p.natDegree - 1 + 1) := by
      exact congrArg (normSq p.leadingCoeff * ·)
        (pow_succ radiusSq (p.natDegree - 1)).symm
    _ = normSq p.leadingCoeff * radiusSq ^ p.natDegree := by
      rw [degreeIdentity]
    _ ≤ normSq ((leadingMonomial p).eval z) := leadingRadial

/-- Explicit positive gap by which the leading monomial dominates the lower
coefficient tail on the computed large-square boundary. -/
def largeSquareDominanceMargin (p : GaussianPolynomial) : Coordinate :=
  (normSq p.leadingCoeff * denseLargeSquareRadius p ^ 2 -
      denseLowerCoefficientWeight p) *
    (denseLargeSquareRadius p ^ 2) ^ (p.natDegree - 1)

theorem largeSquareDominanceMargin_pos
    {p : GaussianPolynomial} (degreePositive : 0 < p.natDegree) :
    0 < largeSquareDominanceMargin p := by
  apply RFAP.ConstructiveFraction.mul_pos_direct
  · exact RFAP.ConstructiveFraction.sub_pos_direct
      (denseLowerCoefficientWeight_lt_leading_radiusSq degreePositive)
  · exact RFAP.ConstructiveFraction.pow_pos_direct (by
      rw [pow_two]
      exact RFAP.ConstructiveFraction.mul_pos_direct
        (denseLargeSquareRadius_pos p) (denseLargeSquareRadius_pos p)) _

/-- Quantitative form of radial dominance, retaining the same finite margin
at every point of the large-square annulus. -/
theorem largeSquare_radial_dominance_margin
    {p : GaussianPolynomial} (degreePositive : 0 < p.natDegree)
    {z : Gaussian}
    (normLower : denseLargeSquareRadius p ^ 2 ≤ normSq z)
    (normUpper : normSq z ≤ 2 * denseLargeSquareRadius p ^ 2) :
    largeSquareDominanceMargin p ≤
      normSq ((leadingMonomial p).eval z) -
        normSq ((lowerTermsPolynomial p).eval z) := by
  let radiusSq := denseLargeSquareRadius p ^ 2
  have radiusSqPositive : 0 < radiusSq := by
    dsimp only [radiusSq]
    rw [pow_two]
    exact RFAP.ConstructiveFraction.mul_pos_direct
      (denseLargeSquareRadius_pos p) (denseLargeSquareRadius_pos p)
  have oneLeRadius := one_le_denseLargeSquareRadius p
  have oneLeRadiusSq : (1 : Coordinate) ≤ radiusSq := by
    dsimp only [radiusSq]
    rw [pow_two]
    calc
      1 = 1 * 1 := by ring1
      _ ≤ denseLargeSquareRadius p * denseLargeSquareRadius p :=
        RFAP.ConstructiveFraction.mul_le_mul_direct oneLeRadius oneLeRadius
          (by decide) (denseLargeSquareRadius_pos p).le
  have lowerTermsBound := normSq_lowerTermsPolynomial_eval_le degreePositive
    (z := z) (radialSq := radiusSq)
    (by simpa only [radiusSq] using normUpper) oneLeRadiusSq
  have leadingBound := normSq_leadingMonomial_eval_lower degreePositive
    radiusSqPositive.le (by simpa only [radiusSq] using normLower)
  have degreeIdentity : p.natDegree - 1 + 1 = p.natDegree := by omega
  apply (le_sub_iff_add_le).2
  calc
    largeSquareDominanceMargin p +
        normSq ((lowerTermsPolynomial p).eval z) ≤
      largeSquareDominanceMargin p +
        denseLowerCoefficientWeight p *
          radiusSq ^ (p.natDegree - 1) :=
      add_le_add (le_refl _) lowerTermsBound
    _ = (normSq p.leadingCoeff * radiusSq) *
          radiusSq ^ (p.natDegree - 1) := by
      dsimp only [largeSquareDominanceMargin, radiusSq]
      ring1
    _ = normSq p.leadingCoeff *
          (radiusSq ^ (p.natDegree - 1) * radiusSq) := by ring1
    _ = normSq p.leadingCoeff *
          radiusSq ^ (p.natDegree - 1 + 1) := by
      exact congrArg (normSq p.leadingCoeff * ·)
        (pow_succ radiusSq (p.natDegree - 1)).symm
    _ = normSq p.leadingCoeff * radiusSq ^ p.natDegree := by
      rw [degreeIdentity]
    _ ≤ normSq ((leadingMonomial p).eval z) := leadingBound

private theorem symmetric_coordinate_sq_bound
    {radius value : Coordinate}
    (lower : -radius ≤ value) (upper : value ≤ radius) :
    value ^ 2 ≤ radius ^ 2 := by
  have bound := RFAP.Boxes.Box.sq_le_endpoint_max lower upper
  have negativeSquare : (-radius) ^ 2 = radius ^ 2 := by ring1
  rw [negativeSquare, max_self] at bound
  exact bound

private theorem horizontal_symmetric_norm_bounds
    {radius value height : Coordinate}
    (valueSquare : value ^ 2 ≤ radius ^ 2)
    (heightSquare : height ^ 2 = radius ^ 2) :
    radius ^ 2 ≤ normSq (point value height) ∧
      normSq (point value height) ≤ 2 * radius ^ 2 := by
  constructor
  · change radius ^ 2 ≤ value ^ 2 + height ^ 2
    rw [heightSquare]
    calc
      radius ^ 2 = 0 + radius ^ 2 := by ring1
      _ ≤ value ^ 2 + radius ^ 2 :=
        add_le_add (RFAP.ConstructiveFraction.sq_nonneg_direct value) le_rfl
  · change value ^ 2 + height ^ 2 ≤ 2 * radius ^ 2
    rw [heightSquare]
    exact (add_le_add valueSquare le_rfl).trans_eq (by ring1)

private theorem vertical_symmetric_norm_bounds
    {radius value width : Coordinate}
    (valueSquare : value ^ 2 ≤ radius ^ 2)
    (widthSquare : width ^ 2 = radius ^ 2) :
    radius ^ 2 ≤ normSq (point width value) ∧
      normSq (point width value) ≤ 2 * radius ^ 2 := by
  constructor
  · change radius ^ 2 ≤ width ^ 2 + value ^ 2
    rw [widthSquare]
    calc
      radius ^ 2 = radius ^ 2 + 0 := by ring1
      _ ≤ radius ^ 2 + value ^ 2 :=
        add_le_add le_rfl
          (RFAP.ConstructiveFraction.sq_nonneg_direct value)
  · change width ^ 2 + value ^ 2 ≤ 2 * radius ^ 2
    rw [widthSquare]
    exact (add_le_add le_rfl valueSquare).trans_eq (by ring1)

private theorem largeSquare_boundary_norm_bounds
    {p : GaussianPolynomial} {z : Gaussian}
    (boundary : RFAP.BoxClearance.OnBoxBoundary
      (largeSquareBox p) z) :
    denseLargeSquareRadius p ^ 2 ≤ normSq z ∧
      normSq z ≤ 2 * denseLargeSquareRadius p ^ 2 := by
  rcases boundary with ⟨inside, side⟩
  change -denseLargeSquareRadius p ≤ z.re ∧
      z.re ≤ denseLargeSquareRadius p ∧
      -denseLargeSquareRadius p ≤ z.im ∧
      z.im ≤ denseLargeSquareRadius p at inside
  change z.re = -denseLargeSquareRadius p ∨
      z.re = denseLargeSquareRadius p ∨
      z.im = -denseLargeSquareRadius p ∨
      z.im = denseLargeSquareRadius p at side
  have realSquare := symmetric_coordinate_sq_bound inside.1 inside.2.1
  have imaginarySquare :=
    symmetric_coordinate_sq_bound inside.2.2.1 inside.2.2.2
  have upper : normSq z ≤ 2 * denseLargeSquareRadius p ^ 2 := by
    change z.re ^ 2 + z.im ^ 2 ≤ _
    exact (add_le_add realSquare imaginarySquare).trans_eq (by ring1)
  refine ⟨?_, upper⟩
  rcases side with onLeft | onRight | onBottom | onTop
  · change denseLargeSquareRadius p ^ 2 ≤ z.re ^ 2 + z.im ^ 2
    rw [onLeft]
    calc
      denseLargeSquareRadius p ^ 2 =
          (-denseLargeSquareRadius p) ^ 2 + 0 := by ring1
      _ ≤ (-denseLargeSquareRadius p) ^ 2 + z.im ^ 2 :=
        add_le_add (le_refl _)
          (RFAP.ConstructiveFraction.sq_nonneg_direct z.im)
  · change denseLargeSquareRadius p ^ 2 ≤ z.re ^ 2 + z.im ^ 2
    rw [onRight]
    exact le_add_of_nonneg_right
      (RFAP.ConstructiveFraction.sq_nonneg_direct z.im)
  · change denseLargeSquareRadius p ^ 2 ≤ z.re ^ 2 + z.im ^ 2
    rw [onBottom]
    calc
      denseLargeSquareRadius p ^ 2 =
          0 + (-denseLargeSquareRadius p) ^ 2 := by ring1
      _ ≤ z.re ^ 2 + (-denseLargeSquareRadius p) ^ 2 :=
        add_le_add
          (RFAP.ConstructiveFraction.sq_nonneg_direct z.re) (le_refl _)
  · change denseLargeSquareRadius p ^ 2 ≤ z.re ^ 2 + z.im ^ 2
    rw [onTop]
    exact le_add_of_nonneg_left
      (RFAP.ConstructiveFraction.sq_nonneg_direct z.re)

/-- The four pointwise side estimates assemble into the one finite margin
record consumed by constructive winding homotopy. -/
def largeSquare_boundaryNormDominance
    {p : GaussianPolynomial} (degreePositive : 0 < p.natDegree) :
    RFAP.WindingHomotopy.BoundaryNormDominance
      (leadingMonomial p) (lowerTermsPolynomial p) (largeSquareBox p) where
  margin := largeSquareDominanceMargin p
  positive := largeSquareDominanceMargin_pos degreePositive
  lower := by
    intro z boundary
    have bounds := largeSquare_boundary_norm_bounds boundary
    exact largeSquare_radial_dominance_margin degreePositive bounds.1 bounds.2

/-- Coefficient-computed positive clearance for the original polynomial on
the complete large-square boundary. -/
def largeSquare_boundaryClearance
    {p : GaussianPolynomial} (degreePositive : 0 < p.natDegree) :
    RFAP.BoxClearance.BoundaryClearance p (largeSquareBox p) := by
  have sumClearance :=
    RFAP.WindingHomotopy.boundaryClearance_add_of_boundaryNormDominance
      (leadingMonomial p) (lowerTermsPolynomial p) (largeSquareBox p)
      (largeSquareBox_proper p)
      (largeSquare_boundaryNormDominance degreePositive)
  have decomposition :=
    leadingMonomial_add_lowerTerms_eq_normalize degreePositive
  apply RFAP.BoxClearance.BoundaryClearance.ofNormalize
  simpa only [decomposition] using sumClearance

theorem largeSquare_bottom_dominance
    {p : GaussianPolynomial} (degreePositive : 0 < p.natDegree)
    {t : Coordinate}
    (lower : -denseLargeSquareRadius p ≤ t)
    (upper : t ≤ denseLargeSquareRadius p) :
    normSq ((lowerTermsPolynomial p).eval
        (point t (-denseLargeSquareRadius p))) <
      normSq ((leadingMonomial p).eval
        (point t (-denseLargeSquareRadius p))) := by
  have bounds := horizontal_symmetric_norm_bounds
    (symmetric_coordinate_sq_bound lower upper)
    (show (-denseLargeSquareRadius p) ^ 2 =
        denseLargeSquareRadius p ^ 2 by ring1)
  exact largeSquare_radial_dominance degreePositive bounds.1 bounds.2

theorem largeSquare_top_dominance
    {p : GaussianPolynomial} (degreePositive : 0 < p.natDegree)
    {t : Coordinate}
    (lower : -denseLargeSquareRadius p ≤ t)
    (upper : t ≤ denseLargeSquareRadius p) :
    normSq ((lowerTermsPolynomial p).eval
        (point t (denseLargeSquareRadius p))) <
      normSq ((leadingMonomial p).eval
        (point t (denseLargeSquareRadius p))) := by
  have bounds := horizontal_symmetric_norm_bounds
    (symmetric_coordinate_sq_bound lower upper) rfl
  exact largeSquare_radial_dominance degreePositive bounds.1 bounds.2

theorem largeSquare_right_dominance
    {p : GaussianPolynomial} (degreePositive : 0 < p.natDegree)
    {t : Coordinate}
    (lower : -denseLargeSquareRadius p ≤ t)
    (upper : t ≤ denseLargeSquareRadius p) :
    normSq ((lowerTermsPolynomial p).eval
        (point (denseLargeSquareRadius p) t)) <
      normSq ((leadingMonomial p).eval
        (point (denseLargeSquareRadius p) t)) := by
  have bounds := vertical_symmetric_norm_bounds
    (symmetric_coordinate_sq_bound lower upper) rfl
  exact largeSquare_radial_dominance degreePositive bounds.1 bounds.2

theorem largeSquare_left_dominance
    {p : GaussianPolynomial} (degreePositive : 0 < p.natDegree)
    {t : Coordinate}
    (lower : -denseLargeSquareRadius p ≤ t)
    (upper : t ≤ denseLargeSquareRadius p) :
    normSq ((lowerTermsPolynomial p).eval
        (point (-denseLargeSquareRadius p) t)) <
      normSq ((leadingMonomial p).eval
        (point (-denseLargeSquareRadius p) t)) := by
  have bounds := vertical_symmetric_norm_bounds
    (symmetric_coordinate_sq_bound lower upper)
    (show (-denseLargeSquareRadius p) ^ 2 =
        denseLargeSquareRadius p ^ 2 by ring1)
  exact largeSquare_radial_dominance degreePositive bounds.1 bounds.2

theorem leadingMonomial_largeSquare_boundaryCoprime
    {p : GaussianPolynomial} (degreePositive : 0 < p.natDegree) :
    BoundaryCoprime (leadingMonomial p) (largeSquareBox p) := by
  have polynomialNonzero := isZero_false_of_natDegree_pos degreePositive
  have leadingNonzero := leadingCoeff_ne_zero polynomialNonzero
  exact (gaussianConstant_boundaryCoprime leadingNonzero (largeSquareBox p)).mul
    (by
      simpa only [largeSquareBox] using
        coordinatePositivePower_symmetric_boundaryCoprime
          (denseLargeSquareRadius_pos p) (p.natDegree - 1))

/-- The raw constructive winding of every positive-degree dense polynomial
on its coefficient-computed square is four times its finite natural degree. -/
theorem quadrupledBoxWinding_largeSquare_eq_degree
    {p : GaussianPolynomial} (degreePositive : 0 < p.natDegree) :
    quadrupledBoxWinding p (largeSquareBox p) =
      (4 : Int) * p.natDegree := by
  have transfer :=
    RFAP.WindingHomotopy.quadrupledBoxWinding_add_of_boundaryNormDominance
      (leadingMonomial p) (lowerTermsPolynomial p) (largeSquareBox p)
      (largeSquareBox_proper p)
      (leadingMonomial_largeSquare_boundaryClearance degreePositive)
      (largeSquare_boundaryNormDominance degreePositive)
  have decomposition :=
    leadingMonomial_add_lowerTerms_eq_normalize degreePositive
  calc
    quadrupledBoxWinding p (largeSquareBox p) =
        quadrupledBoxWinding p.normalize (largeSquareBox p) :=
      (quadrupledBoxWinding_normalize p (largeSquareBox p)).symm
    _ = quadrupledBoxWinding
          (leadingMonomial p + lowerTermsPolynomial p)
          (largeSquareBox p) := by rw [decomposition]
    _ = quadrupledBoxWinding (leadingMonomial p) (largeSquareBox p) :=
      transfer
    _ = (4 : Int) * p.natDegree :=
      quadrupledBoxWinding_leadingMonomial degreePositive

/-- All three finite winding normalizations recover the positive dense
degree on the computed constructive square. -/
theorem largeSquare_winding_eq_degree
    {p : GaussianPolynomial} (degreePositive : 0 < p.natDegree) :
    quadrupledBoxWinding p (largeSquareBox p) =
        (4 : Int) * p.natDegree ∧
      doubledBoxWinding p (largeSquareBox p) =
        (2 : Int) * p.natDegree ∧
      boxWinding p (largeSquareBox p) = p.natDegree := by
  have raw := quadrupledBoxWinding_largeSquare_eq_degree degreePositive
  refine ⟨raw, ?_, ?_⟩
  · rw [doubledBoxWinding, raw]
    omega
  · rw [boxWinding, raw]
    omega

/-! ## A common outer square for several displayed polynomials -/

/-- Any positive symmetric radius at least the coefficient-computed radius
retains strict leading-term dominance on its boundary. -/
theorem symmetric_radial_dominance_of_denseRadius_le
    {p : GaussianPolynomial} (degreePositive : 0 < p.natDegree)
    {radius : Coordinate}
    (radiusLe : denseLargeSquareRadius p ≤ radius)
    {z : Gaussian}
    (normLower : radius ^ 2 ≤ normSq z)
    (normUpper : normSq z ≤ 2 * radius ^ 2) :
    normSq ((lowerTermsPolynomial p).eval z) <
      normSq ((leadingMonomial p).eval z) := by
  let radiusSq := radius ^ 2
  have radiusPositive : 0 < radius :=
    (denseLargeSquareRadius_pos p).trans_le radiusLe
  have radiusSqPositive : 0 < radiusSq := by
    dsimp only [radiusSq]
    rw [pow_two]
    exact RFAP.ConstructiveFraction.mul_pos_direct radiusPositive radiusPositive
  have oneLeRadius : (1 : Coordinate) ≤ radius :=
    (one_le_denseLargeSquareRadius p).trans radiusLe
  have oneLeRadiusSq : (1 : Coordinate) ≤ radiusSq := by
    dsimp only [radiusSq]
    rw [pow_two]
    calc
      1 = 1 * 1 := by ring1
      _ ≤ radius * radius :=
        RFAP.ConstructiveFraction.mul_le_mul_direct oneLeRadius oneLeRadius
          (by decide) radiusPositive.le
  have lowerBound := normSq_lowerTermsPolynomial_eval_le degreePositive
    (z := z) (radialSq := radiusSq)
    (by simpa only [radiusSq] using normUpper) oneLeRadiusSq
  have denseSquareLe : denseLargeSquareRadius p ^ 2 ≤ radiusSq := by
    exact RFAP.ConstructiveFraction.pow_le_pow_direct
      (denseLargeSquareRadius_pos p).le radiusLe 2
  have leadingScaled :
      normSq p.leadingCoeff * denseLargeSquareRadius p ^ 2 ≤
        normSq p.leadingCoeff * radiusSq :=
    RFAP.ConstructiveFraction.mul_le_mul_of_nonneg_left_direct denseSquareLe
      (normSq_nonneg p.leadingCoeff)
  have weightStrict : denseLowerCoefficientWeight p <
      normSq p.leadingCoeff * radiusSq :=
    (denseLowerCoefficientWeight_lt_leading_radiusSq degreePositive).trans_le
      leadingScaled
  have powerPositive := RFAP.ConstructiveFraction.pow_pos_direct
    radiusSqPositive (p.natDegree - 1)
  have scaledStrict := RFAP.ConstructiveFraction.mul_lt_mul_of_pos_right_direct
    weightStrict powerPositive
  have degreeIdentity : p.natDegree - 1 + 1 = p.natDegree := by omega
  have leadingRadial :
      normSq p.leadingCoeff * radiusSq ^ p.natDegree ≤
        normSq ((leadingMonomial p).eval z) :=
    normSq_leadingMonomial_eval_lower degreePositive radiusSqPositive.le
      (by simpa only [radiusSq] using normLower)
  calc
    normSq ((lowerTermsPolynomial p).eval z) ≤
        denseLowerCoefficientWeight p *
          radiusSq ^ (p.natDegree - 1) := lowerBound
    _ < (normSq p.leadingCoeff * radiusSq) *
          radiusSq ^ (p.natDegree - 1) := scaledStrict
    _ = normSq p.leadingCoeff *
          (radiusSq ^ (p.natDegree - 1) * radiusSq) := by ring1
    _ = normSq p.leadingCoeff *
          radiusSq ^ (p.natDegree - 1 + 1) := by
      exact congrArg (normSq p.leadingCoeff * ·)
        (pow_succ radiusSq (p.natDegree - 1)).symm
    _ = normSq p.leadingCoeff * radiusSq ^ p.natDegree := by
      rw [degreeIdentity]
    _ ≤ normSq ((leadingMonomial p).eval z) := leadingRadial

/-- Boundary norm bounds for an arbitrary positive symmetric rational
square. -/
theorem symmetric_boundary_norm_bounds
    {radius : Coordinate} (radiusNonnegative : 0 ≤ radius) {z : Gaussian}
    (boundary : RFAP.BoxClearance.OnBoxBoundary
      (RFAP.Boxes.Box.symmetric radius radiusNonnegative) z) :
    radius ^ 2 ≤ normSq z ∧ normSq z ≤ 2 * radius ^ 2 := by
  rcases boundary with ⟨inside, side⟩
  change -radius ≤ z.re ∧ z.re ≤ radius ∧
      -radius ≤ z.im ∧ z.im ≤ radius at inside
  change z.re = -radius ∨ z.re = radius ∨
      z.im = -radius ∨ z.im = radius at side
  have realSquare := symmetric_coordinate_sq_bound inside.1 inside.2.1
  have imaginarySquare :=
    symmetric_coordinate_sq_bound inside.2.2.1 inside.2.2.2
  have upper : normSq z ≤ 2 * radius ^ 2 := by
    change z.re ^ 2 + z.im ^ 2 ≤ _
    exact (add_le_add realSquare imaginarySquare).trans_eq (by ring1)
  refine ⟨?_, upper⟩
  rcases side with onLeft | onRight | onBottom | onTop
  · change radius ^ 2 ≤ z.re ^ 2 + z.im ^ 2
    rw [onLeft]
    calc
      radius ^ 2 = (-radius) ^ 2 + 0 := by ring1
      _ ≤ (-radius) ^ 2 + z.im ^ 2 :=
        add_le_add le_rfl (RFAP.ConstructiveFraction.sq_nonneg_direct z.im)
  · change radius ^ 2 ≤ z.re ^ 2 + z.im ^ 2
    rw [onRight]
    exact le_add_of_nonneg_right
      (RFAP.ConstructiveFraction.sq_nonneg_direct z.im)
  · change radius ^ 2 ≤ z.re ^ 2 + z.im ^ 2
    rw [onBottom]
    calc
      radius ^ 2 = 0 + (-radius) ^ 2 := by ring1
      _ ≤ z.re ^ 2 + (-radius) ^ 2 :=
        add_le_add (RFAP.ConstructiveFraction.sq_nonneg_direct z.re) le_rfl
  · change radius ^ 2 ≤ z.re ^ 2 + z.im ^ 2
    rw [onTop]
    exact le_add_of_nonneg_left
      (RFAP.ConstructiveFraction.sq_nonneg_direct z.re)

/-- Explicit dominance margin on an arbitrary sufficiently large symmetric
square. -/
def symmetricDominanceMargin
    (p : GaussianPolynomial) (radius : Coordinate) : Coordinate :=
  (normSq p.leadingCoeff * radius ^ 2 -
      denseLowerCoefficientWeight p) *
    (radius ^ 2) ^ (p.natDegree - 1)

theorem symmetricDominanceMargin_pos
    {p : GaussianPolynomial} (degreePositive : 0 < p.natDegree)
    {radius : Coordinate}
    (radiusLe : denseLargeSquareRadius p ≤ radius) :
    0 < symmetricDominanceMargin p radius := by
  have radiusPositive := (denseLargeSquareRadius_pos p).trans_le radiusLe
  have denseSquareLe : denseLargeSquareRadius p ^ 2 ≤ radius ^ 2 :=
    RFAP.ConstructiveFraction.pow_le_pow_direct
      (denseLargeSquareRadius_pos p).le radiusLe 2
  have leadingScaled :
      normSq p.leadingCoeff * denseLargeSquareRadius p ^ 2 ≤
        normSq p.leadingCoeff * radius ^ 2 :=
    RFAP.ConstructiveFraction.mul_le_mul_of_nonneg_left_direct denseSquareLe
      (normSq_nonneg p.leadingCoeff)
  have weightStrict : denseLowerCoefficientWeight p <
      normSq p.leadingCoeff * radius ^ 2 :=
    (denseLowerCoefficientWeight_lt_leading_radiusSq degreePositive).trans_le
      leadingScaled
  apply RFAP.ConstructiveFraction.mul_pos_direct
  · exact RFAP.ConstructiveFraction.sub_pos_direct weightStrict
  · exact RFAP.ConstructiveFraction.pow_pos_direct (by
      rw [pow_two]
      exact RFAP.ConstructiveFraction.mul_pos_direct radiusPositive
        radiusPositive) _

theorem symmetric_radial_dominance_margin
    {p : GaussianPolynomial} (degreePositive : 0 < p.natDegree)
    {radius : Coordinate}
    (radiusLe : denseLargeSquareRadius p ≤ radius)
    {z : Gaussian}
    (normLower : radius ^ 2 ≤ normSq z)
    (normUpper : normSq z ≤ 2 * radius ^ 2) :
    symmetricDominanceMargin p radius ≤
      normSq ((leadingMonomial p).eval z) -
        normSq ((lowerTermsPolynomial p).eval z) := by
  let radiusSq := radius ^ 2
  have radiusPositive := (denseLargeSquareRadius_pos p).trans_le radiusLe
  have radiusSqPositive : 0 < radiusSq := by
    dsimp only [radiusSq]
    rw [pow_two]
    exact RFAP.ConstructiveFraction.mul_pos_direct radiusPositive radiusPositive
  have oneLeRadius : (1 : Coordinate) ≤ radius :=
    (one_le_denseLargeSquareRadius p).trans radiusLe
  have oneLeRadiusSq : (1 : Coordinate) ≤ radiusSq := by
    dsimp only [radiusSq]
    rw [pow_two]
    exact RFAP.ConstructiveFraction.mul_le_mul_direct oneLeRadius oneLeRadius
      (by decide) radiusPositive.le
  have lowerTermsBound := normSq_lowerTermsPolynomial_eval_le degreePositive
    (z := z) (radialSq := radiusSq)
    (by simpa only [radiusSq] using normUpper) oneLeRadiusSq
  have leadingBound := normSq_leadingMonomial_eval_lower degreePositive
    radiusSqPositive.le (by simpa only [radiusSq] using normLower)
  have degreeIdentity : p.natDegree - 1 + 1 = p.natDegree := by omega
  apply (le_sub_iff_add_le).2
  calc
    symmetricDominanceMargin p radius +
        normSq ((lowerTermsPolynomial p).eval z) ≤
      symmetricDominanceMargin p radius +
        denseLowerCoefficientWeight p *
          radiusSq ^ (p.natDegree - 1) :=
      add_le_add le_rfl lowerTermsBound
    _ = (normSq p.leadingCoeff * radiusSq) *
          radiusSq ^ (p.natDegree - 1) := by
      dsimp only [symmetricDominanceMargin, radiusSq]
      ring1
    _ = normSq p.leadingCoeff *
          (radiusSq ^ (p.natDegree - 1) * radiusSq) := by ring1
    _ = normSq p.leadingCoeff *
          radiusSq ^ (p.natDegree - 1 + 1) := by
      exact congrArg (normSq p.leadingCoeff * ·)
        (pow_succ radiusSq (p.natDegree - 1)).symm
    _ = normSq p.leadingCoeff * radiusSq ^ p.natDegree := by
      rw [degreeIdentity]
    _ ≤ normSq ((leadingMonomial p).eval z) := leadingBound

/-- Quantitative leading-term dominance on a common positive symmetric
square. -/
def symmetric_boundaryNormDominance
    {p : GaussianPolynomial} (degreePositive : 0 < p.natDegree)
    {radius : Coordinate}
    (radiusLe : denseLargeSquareRadius p ≤ radius) :
    RFAP.WindingHomotopy.BoundaryNormDominance
      (leadingMonomial p) (lowerTermsPolynomial p)
      (RFAP.Boxes.Box.symmetric radius
        ((denseLargeSquareRadius_pos p).trans_le radiusLe).le) where
  margin := symmetricDominanceMargin p radius
  positive := symmetricDominanceMargin_pos degreePositive radiusLe
  lower := by
    intro z boundary
    have bounds := symmetric_boundary_norm_bounds
      ((denseLargeSquareRadius_pos p).trans_le radiusLe).le boundary
    exact symmetric_radial_dominance_margin degreePositive radiusLe
      bounds.1 bounds.2

/-- A polynomial has a coefficient-computed positive clearance on every
positive symmetric square at least as large as its own large-square radius.
This is the clearance companion to `quadrupledBoxWinding_symmetric_eq_degree`
and lets finitely many polynomials share one outer boundary. -/
def symmetric_boundaryClearance
    {p : GaussianPolynomial} (degreePositive : 0 < p.natDegree)
    {radius : Coordinate}
    (radiusLe : denseLargeSquareRadius p ≤ radius) :
    RFAP.BoxClearance.BoundaryClearance p
      (RFAP.Boxes.Box.symmetric radius
        ((denseLargeSquareRadius_pos p).trans_le radiusLe).le) := by
  let radiusPositive := (denseLargeSquareRadius_pos p).trans_le radiusLe
  let box := RFAP.Boxes.Box.symmetric radius radiusPositive.le
  have proper : box.Proper := by
    change -radius < radius ∧ -radius < radius
    exact ⟨(neg_lt_zero.mpr radiusPositive).trans radiusPositive,
      (neg_lt_zero.mpr radiusPositive).trans radiusPositive⟩
  have sumClearance :=
    RFAP.WindingHomotopy.boundaryClearance_add_of_boundaryNormDominance
      (leadingMonomial p) (lowerTermsPolynomial p) box proper
      (symmetric_boundaryNormDominance degreePositive radiusLe)
  have decomposition := leadingMonomial_add_lowerTerms_eq_normalize
    degreePositive
  apply RFAP.BoxClearance.BoundaryClearance.ofNormalize
  simpa only [box, decomposition] using sumClearance

/-- The leading monomial has degree winding on every positive symmetric
square, independently of the polynomial-specific computed radius. -/
theorem quadrupledBoxWinding_leadingMonomial_symmetric
    {p : GaussianPolynomial} (degreePositive : 0 < p.natDegree)
    {radius : Coordinate} (radiusPositive : 0 < radius) :
    quadrupledBoxWinding (leadingMonomial p)
        (RFAP.Boxes.Box.symmetric radius radiusPositive.le) =
      (4 : Int) * p.natDegree := by
  have polynomialNonzero := isZero_false_of_natDegree_pos degreePositive
  have leadingNonzero := leadingCoeff_ne_zero polynomialNonzero
  have product :=
    RFAP.WindingProduct.quadrupledBoxWinding_mul_of_boundaryClearances
      (gaussianConstant p.leadingCoeff)
      (coordinatePositivePower (p.natDegree - 1))
      (RFAP.Boxes.Box.symmetric radius radiusPositive.le)
      (by
        change -radius < radius ∧ -radius < radius
        exact ⟨(neg_lt_zero.mpr radiusPositive).trans radiusPositive,
          (neg_lt_zero.mpr radiusPositive).trans radiusPositive⟩)
      (gaussianConstant_boundaryClearance leadingNonzero _)
      (coordinatePositivePower_symmetric_boundaryClearance radiusPositive _)
  have powerWinding := quadrupledBoxWinding_coordinatePositivePower
    radiusPositive (p.natDegree - 1)
  change quadrupledBoxWinding
      (gaussianConstant p.leadingCoeff *
        coordinatePositivePower (p.natDegree - 1))
      (RFAP.Boxes.Box.symmetric radius radiusPositive.le) =
        (4 : Int) * p.natDegree
  rw [product,
    quadrupledBoxWinding_gaussianConstant leadingNonzero _]
  rw [powerWinding]
  omega

/-- A polynomial has raw winding four times its degree on every positive
symmetric square at least as large as its computed coefficient radius. -/
theorem quadrupledBoxWinding_symmetric_eq_degree
    {p : GaussianPolynomial} (degreePositive : 0 < p.natDegree)
    {radius : Coordinate}
    (radiusLe : denseLargeSquareRadius p ≤ radius) :
    quadrupledBoxWinding p
        (RFAP.Boxes.Box.symmetric radius
          ((denseLargeSquareRadius_pos p).trans_le radiusLe).le) =
      (4 : Int) * p.natDegree := by
  let radiusPositive := (denseLargeSquareRadius_pos p).trans_le radiusLe
  let box := RFAP.Boxes.Box.symmetric radius radiusPositive.le
  have proper : box.Proper := by
    change -radius < radius ∧ -radius < radius
    exact ⟨(neg_lt_zero.mpr radiusPositive).trans radiusPositive,
      (neg_lt_zero.mpr radiusPositive).trans radiusPositive⟩
  have leadingClearance :
      RFAP.BoxClearance.BoundaryClearance
        (leadingMonomial p) box := by
    have polynomialNonzero := isZero_false_of_natDegree_pos degreePositive
    have leadingNonzero := leadingCoeff_ne_zero polynomialNonzero
    exact RFAP.BoxClearance.BoundaryClearance.mul
      (gaussianConstant_boundaryClearance leadingNonzero box)
      (by
        simpa only [box] using
          coordinatePositivePower_symmetric_boundaryClearance
            radiusPositive (p.natDegree - 1))
  have transfer :=
    RFAP.WindingHomotopy.quadrupledBoxWinding_add_of_boundaryNormDominance
      (leadingMonomial p) (lowerTermsPolynomial p) box proper
      leadingClearance (symmetric_boundaryNormDominance degreePositive radiusLe)
  have decomposition := leadingMonomial_add_lowerTerms_eq_normalize
    degreePositive
  calc
    quadrupledBoxWinding p box = quadrupledBoxWinding p.normalize box :=
      (quadrupledBoxWinding_normalize p box).symm
    _ = quadrupledBoxWinding
          (leadingMonomial p + lowerTermsPolynomial p) box := by
      rw [decomposition]
    _ = quadrupledBoxWinding (leadingMonomial p) box := transfer
    _ = (4 : Int) * p.natDegree :=
      quadrupledBoxWinding_leadingMonomial_symmetric
        degreePositive radiusPositive

/-- Every displayed nonzero polynomial has positive boundary clearance on a
sufficiently large symmetric square.  The degree-zero branch is handled by
its exact normalized constant; no positive-degree hypothesis is hidden in
the public statement. -/
def symmetric_boundaryClearance_of_nonzero
    {p : GaussianPolynomial} (nonzero : p.isZero = false)
    {radius : Coordinate}
    (radiusLe : denseLargeSquareRadius p ≤ radius) :
    RFAP.BoxClearance.BoundaryClearance p
      (RFAP.Boxes.Box.symmetric radius
        ((denseLargeSquareRadius_pos p).trans_le radiusLe).le) := by
  by_cases degreeZero : p.natDegree = 0
  · apply RFAP.BoxClearance.BoundaryClearance.ofNormalize
    have normalizedConstant :
        p.normalize = gaussianConstant p.leadingCoeff :=
      normalize_eq_constant_leadingCoeff_of_degree_zero nonzero degreeZero
    rw [normalizedConstant]
    exact gaussianConstant_boundaryClearance
      (leadingCoeff_ne_zero nonzero) _
  · exact symmetric_boundaryClearance (Nat.pos_of_ne_zero degreeZero)
      radiusLe

/-- On every sufficiently large positive symmetric square, the raw winding
of a nonzero polynomial is four times its natural degree, including the
constant case where both sides are zero. -/
theorem quadrupledBoxWinding_symmetric_eq_degree_of_nonzero
    {p : GaussianPolynomial} (nonzero : p.isZero = false)
    {radius : Coordinate}
    (radiusLe : denseLargeSquareRadius p ≤ radius) :
    quadrupledBoxWinding p
        (RFAP.Boxes.Box.symmetric radius
          ((denseLargeSquareRadius_pos p).trans_le radiusLe).le) =
      (4 : Int) * p.natDegree := by
  by_cases degreeZero : p.natDegree = 0
  · have normalizedConstant :
        p.normalize = gaussianConstant p.leadingCoeff :=
      normalize_eq_constant_leadingCoeff_of_degree_zero nonzero degreeZero
    calc
      quadrupledBoxWinding p
          (RFAP.Boxes.Box.symmetric radius
            ((denseLargeSquareRadius_pos p).trans_le radiusLe).le) =
          quadrupledBoxWinding p.normalize
            (RFAP.Boxes.Box.symmetric radius
              ((denseLargeSquareRadius_pos p).trans_le radiusLe).le) :=
        (quadrupledBoxWinding_normalize p _).symm
      _ = quadrupledBoxWinding (gaussianConstant p.leadingCoeff)
            (RFAP.Boxes.Box.symmetric radius
              ((denseLargeSquareRadius_pos p).trans_le radiusLe).le) := by
        rw [normalizedConstant]
      _ = 0 := quadrupledBoxWinding_gaussianConstant
        (leadingCoeff_ne_zero nonzero) _
      _ = (4 : Int) * p.natDegree := by rw [degreeZero]; rfl
  · exact quadrupledBoxWinding_symmetric_eq_degree
      (Nat.pos_of_ne_zero degreeZero) radiusLe

end RFAP.GlobalWinding
