import RationalRotations.QuaternionObstruction
import RationalRotations.RationalSurjectivity
import mathlib.RFAP.ConstructiveNatSqrt

/-!
# Finite rational approximation by unit-quaternion rotations

This module proves the finite-precision form of the density clause in Problem
70.  It uses squared error on the nine displayed matrix entries, a finite
integer-square-root bracket, and a rational stereographic candidate whose norm
is exactly one.  Every positive rational radius request terminates with a
strict error certificate.  No real square root, topology, sequence, or limit
is formed.
-/

namespace RationalRotations

namespace FiniteKernelApproximation

abbrev Scalar := RFAP.ConstructiveFraction.Rational

/-- A positive canonical rational is strictly below one plus its displayed
natural numerator.  This is the finite Archimedean step used to choose a
refinement; it is proved by multiplying through the stored positive
denominator. -/
private theorem positiveRational_lt_numerator_succ
    (value : Scalar) (positive : 0 < value) :
    value < (value.num.toNat + 1 : Nat) := by
  have numeratorPositive : (0 : Int) < value.num :=
    (RFAP.CanonicalFraction.zero_lt_iff_num_pos value).mp positive
  have numeratorNonnegative : (0 : Int) ≤ value.num :=
    Int.le_of_lt numeratorPositive
  have numeratorCast : (value.num.toNat : Scalar) =
      (value.num : Scalar) := by
    have integerEquality : (value.num.toNat : Int) = value.num :=
      Int.toNat_of_nonneg numeratorNonnegative
    simpa only [Int.cast_natCast] using
      congrArg (fun integer : Int => (integer : Scalar)) integerEquality
  have denominatorPositive : (0 : Scalar) < (value.den : Scalar) :=
    RFAP.ConstructiveFraction.natCast_pos_direct value.den_pos
  apply RFAP.ConstructiveFraction.lt_of_mul_lt_mul_right_direct
    (c := (value.den : Scalar)) _ denominatorPositive
  change value *
      ((RFAP.ConstructiveFraction.representative value).den : Scalar) < _
  rw [RFAP.ConstructiveFraction.representative_mul_den value]
  have naturalCleared : value.num.toNat <
      (value.num.toNat + 1) * value.den := by
    have denominatorAtLeastOne : 1 ≤ value.den := value.den_pos
    calc
      value.num.toNat < value.num.toNat + 1 := Nat.lt_succ_self _
      _ = (value.num.toNat + 1) * 1 := by omega0
      _ ≤ (value.num.toNat + 1) * value.den :=
        Nat.mul_le_mul_left (value.num.toNat + 1) denominatorAtLeastOne
  have castCleared :=
    RFAP.ConstructiveFraction.natCast_lt_direct naturalCleared
  change (value.num : Scalar) < _
  simpa only [Nat.cast_mul, Nat.cast_add, Nat.cast_one, numeratorCast] using
    castCleared

/-! ## Exact rational matrix error -/

/-- Squared Frobenius error of two displayed rational matrices. -/
def matrixDistanceSq (left right : Matrix3 Scalar) : Scalar :=
  (left.tt - right.tt) ^ 2 +
  (left.tr - right.tr) ^ 2 +
  (left.ts - right.ts) ^ 2 +
  (left.rt - right.rt) ^ 2 +
  (left.rr - right.rr) ^ 2 +
  (left.rs - right.rs) ^ 2 +
  (left.st - right.st) ^ 2 +
  (left.sr - right.sr) ^ 2 +
  (left.ss - right.ss) ^ 2

theorem matrixDistanceSq_nonnegative (left right : Matrix3 Scalar) :
    0 ≤ matrixDistanceSq left right := by
  unfold matrixDistanceSq
  have tt := RFAP.ConstructiveFraction.sq_nonneg_direct
    (left.tt - right.tt)
  have tr := RFAP.ConstructiveFraction.sq_nonneg_direct
    (left.tr - right.tr)
  have ts := RFAP.ConstructiveFraction.sq_nonneg_direct
    (left.ts - right.ts)
  have rt := RFAP.ConstructiveFraction.sq_nonneg_direct
    (left.rt - right.rt)
  have rr := RFAP.ConstructiveFraction.sq_nonneg_direct
    (left.rr - right.rr)
  have rs := RFAP.ConstructiveFraction.sq_nonneg_direct
    (left.rs - right.rs)
  have st := RFAP.ConstructiveFraction.sq_nonneg_direct
    (left.st - right.st)
  have sr := RFAP.ConstructiveFraction.sq_nonneg_direct
    (left.sr - right.sr)
  have ss := RFAP.ConstructiveFraction.sq_nonneg_direct
    (left.ss - right.ss)
  exact add_nonneg
    (add_nonneg
      (add_nonneg
        (add_nonneg
          (add_nonneg
            (add_nonneg
              (add_nonneg (add_nonneg tt tr) ts) rt) rr) rs) st) sr) ss

theorem matrixDistanceSq_self (matrix : Matrix3 Scalar) :
    matrixDistanceSq matrix matrix = 0 := by
  unfold matrixDistanceSq
  ring1

/-- For displayed rotations, squared entrywise error is determined by the
trace of their relative rotation. -/
theorem matrixDistanceSq_eq_six_sub_two_trace_mul_transpose
    (left right : Rotation Scalar) :
    matrixDistanceSq left.matrix right.matrix =
      6 - 2 * Matrix3.trace
        (Matrix3.mul left.matrix (Matrix3.transpose right.matrix)) := by
  have leftFirst := congrArg (fun matrix : Matrix3 Scalar => matrix.tt)
    left.orthogonal
  have leftSecond := congrArg (fun matrix : Matrix3 Scalar => matrix.rr)
    left.orthogonal
  have leftThird := congrArg (fun matrix : Matrix3 Scalar => matrix.ss)
    left.orthogonal
  have rightFirst := congrArg (fun matrix : Matrix3 Scalar => matrix.tt)
    right.orthogonal
  have rightSecond := congrArg (fun matrix : Matrix3 Scalar => matrix.rr)
    right.orthogonal
  have rightThird := congrArg (fun matrix : Matrix3 Scalar => matrix.ss)
    right.orthogonal
  change left.matrix.tt * left.matrix.tt +
      left.matrix.tr * left.matrix.tr +
      left.matrix.ts * left.matrix.ts = 1 at leftFirst
  change left.matrix.rt * left.matrix.rt +
      left.matrix.rr * left.matrix.rr +
      left.matrix.rs * left.matrix.rs = 1 at leftSecond
  change left.matrix.st * left.matrix.st +
      left.matrix.sr * left.matrix.sr +
      left.matrix.ss * left.matrix.ss = 1 at leftThird
  change right.matrix.tt * right.matrix.tt +
      right.matrix.tr * right.matrix.tr +
      right.matrix.ts * right.matrix.ts = 1 at rightFirst
  change right.matrix.rt * right.matrix.rt +
      right.matrix.rr * right.matrix.rr +
      right.matrix.rs * right.matrix.rs = 1 at rightSecond
  change right.matrix.st * right.matrix.st +
      right.matrix.sr * right.matrix.sr +
      right.matrix.ss * right.matrix.ss = 1 at rightThird
  calc
    matrixDistanceSq left.matrix right.matrix =
        (left.matrix.tt * left.matrix.tt +
          left.matrix.tr * left.matrix.tr +
          left.matrix.ts * left.matrix.ts) +
        (left.matrix.rt * left.matrix.rt +
          left.matrix.rr * left.matrix.rr +
          left.matrix.rs * left.matrix.rs) +
        (left.matrix.st * left.matrix.st +
          left.matrix.sr * left.matrix.sr +
          left.matrix.ss * left.matrix.ss) +
        (right.matrix.tt * right.matrix.tt +
          right.matrix.tr * right.matrix.tr +
          right.matrix.ts * right.matrix.ts) +
        (right.matrix.rt * right.matrix.rt +
          right.matrix.rr * right.matrix.rr +
          right.matrix.rs * right.matrix.rs) +
        (right.matrix.st * right.matrix.st +
          right.matrix.sr * right.matrix.sr +
          right.matrix.ss * right.matrix.ss) -
        2 * Matrix3.trace
          (Matrix3.mul left.matrix (Matrix3.transpose right.matrix)) := by
      unfold matrixDistanceSq Matrix3.trace Matrix3.mul Matrix3.transpose
      ring1
    _ = 6 - 2 * Matrix3.trace
        (Matrix3.mul left.matrix (Matrix3.transpose right.matrix)) := by
      rw [leftFirst, leftSecond, leftThird, rightFirst, rightSecond,
        rightThird]
      ring1

/-- Quaternion conjugation displays the transpose inverse rotation. -/
theorem conjugate_rotationMatrix (proportion : NonNullProportion Scalar) :
    (NonNullProportion.conjugate proportion).rotationMatrix =
      Matrix3.transpose proportion.rotationMatrix := by
  rw [NonNullProportion.rotationMatrix_eq_scaled_numerator,
    NonNullProportion.rotationMatrix_eq_scaled_numerator]
  change Matrix3.scale
      (Proportion.norm (Proportion.conjugate proportion.toProportion))⁻¹
      (proportionRotationNumerator
        (Proportion.conjugate proportion.toProportion)) =
    Matrix3.transpose
      (Matrix3.scale proportion.toProportion.norm⁻¹
        (proportionRotationNumerator proportion.toProportion))
  rw [Proportion.norm_conjugate, Matrix3.transpose_scale]
  apply Matrix3.ext <;>
    unfold proportionRotationNumerator Proportion.conjugate Matrix3.scale
      Matrix3.transpose Vector.neg <;> ring1

/-- Squared matrix error is eight times the half spread of the relative
quaternion rotation. -/
theorem matrixDistanceSq_eq_eight_mul_halfSpread_relative
    (left right : NonNullProportion Scalar) :
    matrixDistanceSq left.rotationMatrix right.rotationMatrix =
      8 * halfSpread
        (NonNullProportion.mul left
          (NonNullProportion.conjugate right)).rotation := by
  change matrixDistanceSq left.rotation.matrix right.rotation.matrix = _
  rw [matrixDistanceSq_eq_six_sub_two_trace_mul_transpose]
  change 6 - 2 * Matrix3.trace
      (Matrix3.mul left.rotationMatrix
        (Matrix3.transpose right.rotationMatrix)) = _
  rw [← conjugate_rotationMatrix right,
    ← NonNullProportion.rotationMatrix_mul]
  have fourCancel : (4 : Scalar) * (4 : Scalar)⁻¹ = 1 :=
    RFAP.ExplicitField.mul_inv_cancel 4 (by decide)
  unfold halfSpread NonNullProportion.rotation
  simp only [RFAP.ExplicitField.div_eq_mul_inv]
  calc
    6 - 2 * Matrix3.trace
        (NonNullProportion.mul left
          (NonNullProportion.conjugate right)).rotationMatrix =
      2 * (3 - Matrix3.trace
        (NonNullProportion.mul left
          (NonNullProportion.conjugate right)).rotationMatrix) := by ring1
    _ = 8 * ((3 - Matrix3.trace
        (NonNullProportion.mul left
          (NonNullProportion.conjugate right)).rotationMatrix) *
          (4 : Scalar)⁻¹) := by
      calc
        2 * (3 - Matrix3.trace
            (NonNullProportion.mul left
              (NonNullProportion.conjugate right)).rotationMatrix) =
          2 * (3 - Matrix3.trace
            (NonNullProportion.mul left
              (NonNullProportion.conjugate right)).rotationMatrix) *
            (4 * (4 : Scalar)⁻¹) := by rw [fourCancel]; ring1
        _ = 8 * ((3 - Matrix3.trace
            (NonNullProportion.mul left
              (NonNullProportion.conjugate right)).rotationMatrix) *
              (4 : Scalar)⁻¹) := by ring1

/-! ## Finite square-root brackets -/

private theorem nat_square_div_le_div
    {root numerator rootDenominator valueDenominator : Nat}
    (rootDenominatorPositive : 0 < rootDenominator)
    (valueDenominatorPositive : 0 < valueDenominator)
    (cleared : root ^ 2 * valueDenominator ≤
      numerator * rootDenominator ^ 2) :
    ((root : Scalar) / (rootDenominator : Scalar)) ^ 2 ≤
      (numerator : Scalar) / (valueDenominator : Scalar) := by
  have rootDenominatorCastPositive :=
    RFAP.ConstructiveFraction.natCast_pos_direct rootDenominatorPositive
  have valueDenominatorCastPositive :=
    RFAP.ConstructiveFraction.natCast_pos_direct valueDenominatorPositive
  rw [show ((root : Scalar) / (rootDenominator : Scalar)) ^ 2 =
      (root : Scalar) ^ 2 / (rootDenominator : Scalar) ^ 2 by
    simp only [RFAP.ExplicitField.div_eq_mul_inv]
    rw [RFAP.ConstructiveFraction.inv_pow_direct]
    ring1]
  apply (RFAP.ConstructiveFraction.div_le_iff_pos
    (RFAP.ConstructiveFraction.pow_pos_direct
      rootDenominatorCastPositive 2)).2
  rw [show ((numerator : Scalar) / (valueDenominator : Scalar)) *
      (rootDenominator : Scalar) ^ 2 =
      ((numerator : Scalar) * (rootDenominator : Scalar) ^ 2) /
        (valueDenominator : Scalar) by
    simp only [RFAP.ExplicitField.div_eq_mul_inv]
    ring1]
  apply (RFAP.ConstructiveFraction.le_div_iff_pos
    valueDenominatorCastPositive).2
  have castCleared := RFAP.ConstructiveFraction.natCast_le_direct cleared
  simpa only [Nat.cast_mul, Nat.cast_pow] using castCleared

private theorem nat_div_lt_square_div
    {numerator upper rootDenominator valueDenominator : Nat}
    (rootDenominatorPositive : 0 < rootDenominator)
    (valueDenominatorPositive : 0 < valueDenominator)
    (cleared : numerator * rootDenominator ^ 2 <
      upper ^ 2 * valueDenominator) :
    (numerator : Scalar) / (valueDenominator : Scalar) <
      ((upper : Scalar) / (rootDenominator : Scalar)) ^ 2 := by
  have rootDenominatorCastPositive :=
    RFAP.ConstructiveFraction.natCast_pos_direct rootDenominatorPositive
  have valueDenominatorCastPositive :=
    RFAP.ConstructiveFraction.natCast_pos_direct valueDenominatorPositive
  rw [show ((upper : Scalar) / (rootDenominator : Scalar)) ^ 2 =
      (upper : Scalar) ^ 2 / (rootDenominator : Scalar) ^ 2 by
    simp only [RFAP.ExplicitField.div_eq_mul_inv]
    rw [RFAP.ConstructiveFraction.inv_pow_direct]
    ring1]
  apply (RFAP.ConstructiveFraction.lt_div_iff_pos
    (RFAP.ConstructiveFraction.pow_pos_direct
      rootDenominatorCastPositive 2)).2
  rw [show ((numerator : Scalar) / (valueDenominator : Scalar)) *
      (rootDenominator : Scalar) ^ 2 =
      ((numerator : Scalar) * (rootDenominator : Scalar) ^ 2) /
        (valueDenominator : Scalar) by
    simp only [RFAP.ExplicitField.div_eq_mul_inv]
    ring1]
  apply (RFAP.ConstructiveFraction.div_lt_iff_pos
    valueDenominatorCastPositive).2
  have castCleared := RFAP.ConstructiveFraction.natCast_lt_direct cleared
  simpa only [Nat.cast_mul, Nat.cast_pow] using castCleared

/-- Cached finite bracket around the positive square root of one displayed
rational target.  The parameter `scale` requests denominator refinement by
the positive factor `scale + 1`. -/
structure SqrtBracket
    (target : TheoremSixtyTwo.PositiveSquareClassRepresentative)
    (scale : Nat) where
  radicand : Nat
  radicand_eq : radicand = target.numerator * target.denominator *
    (scale + 1) ^ 2
  lowerNumerator : Nat
  lowerNumerator_eq : lowerNumerator =
    RFAP.ConstructiveNatSqrt.floor radicand
  denominator : Nat
  denominator_eq : denominator = target.denominator * (scale + 1)
  denominator_positive : 0 < denominator
  lower : Scalar
  lower_eq : lower = (lowerNumerator : Scalar) / (denominator : Scalar)
  upper : Scalar
  upper_eq : upper = (lowerNumerator + 1 : Nat) / (denominator : Scalar)
  lower_nonnegative : 0 ≤ lower
  upper_positive : 0 < upper
  lower_square_le : lower ^ 2 ≤ target.representative.value
  value_lt_upper_square : target.representative.value < upper ^ 2
  width_eq : upper - lower = 1 / (denominator : Scalar)

/-- Compute one finite square-root bracket at the requested denominator
scale.  The project-owned square root uses logarithmic base-four recursion,
and its two integer bounds are consumed directly. -/
def sqrtBracket
    (target : TheoremSixtyTwo.PositiveSquareClassRepresentative)
    (scale : Nat) : SqrtBracket target scale := by
  let refinement := scale + 1
  let radicand := target.numerator * target.denominator * refinement ^ 2
  let lowerNumerator := RFAP.ConstructiveNatSqrt.floor radicand
  let denominator := target.denominator * refinement
  have refinementPositive : 0 < refinement := by
    unfold refinement
    omega0
  have denominatorPositive : 0 < denominator := by
    unfold denominator
    exact Nat.mul_pos target.denominator_positive refinementPositive
  have lowerNatural : lowerNumerator ^ 2 ≤ radicand := by
    unfold lowerNumerator
    exact RFAP.ConstructiveNatSqrt.floor_square_le radicand
  have upperNatural : radicand < (lowerNumerator + 1) ^ 2 := by
    unfold lowerNumerator
    exact RFAP.ConstructiveNatSqrt.lt_floor_succ_square radicand
  have lowerCleared : lowerNumerator ^ 2 * target.denominator ≤
      target.numerator * denominator ^ 2 := by
    calc
      lowerNumerator ^ 2 * target.denominator ≤
          radicand * target.denominator :=
        Nat.mul_le_mul_right target.denominator lowerNatural
      _ = target.numerator * denominator ^ 2 := by
        unfold radicand denominator
        ring1
  have upperCleared : target.numerator * denominator ^ 2 <
      (lowerNumerator + 1) ^ 2 * target.denominator := by
    calc
      target.numerator * denominator ^ 2 =
          radicand * target.denominator := by
        unfold radicand denominator
        ring1
      _ < (lowerNumerator + 1) ^ 2 * target.denominator :=
        Nat.mul_lt_mul_of_pos_right upperNatural target.denominator_positive
  let lower : Scalar := (lowerNumerator : Scalar) / (denominator : Scalar)
  let upper : Scalar :=
    (lowerNumerator + 1 : Nat) / (denominator : Scalar)
  refine
    { radicand := radicand
      radicand_eq := rfl
      lowerNumerator := lowerNumerator
      lowerNumerator_eq := rfl
      denominator := denominator
      denominator_eq := rfl
      denominator_positive := denominatorPositive
      lower := lower
      lower_eq := rfl
      upper := upper
      upper_eq := rfl
      lower_nonnegative := ?_
      upper_positive := ?_
      lower_square_le := ?_
      value_lt_upper_square := ?_
      width_eq := ?_ }
  · unfold lower
    exact RFAP.ConstructiveFraction.div_nonneg_direct
      (RFAP.ConstructiveFraction.natCast_le_direct (Nat.zero_le _))
      (RFAP.ConstructiveFraction.natCast_le_direct
        denominatorPositive.le)
  · unfold upper
    exact RFAP.ConstructiveFraction.div_pos_direct
      (RFAP.ConstructiveFraction.natCast_pos_direct (by omega0))
      (RFAP.ConstructiveFraction.natCast_pos_direct denominatorPositive)
  · unfold lower
    rw [target.value_eq_div]
    exact nat_square_div_le_div denominatorPositive
      target.denominator_positive lowerCleared
  · unfold upper
    rw [target.value_eq_div]
    exact nat_div_lt_square_div denominatorPositive
      target.denominator_positive upperCleared
  · unfold lower upper
    simp only [Nat.cast_add, Nat.cast_one,
      RFAP.ExplicitField.div_eq_mul_inv]
    ring1

/-- The upper-square error is bounded by a simple reciprocal refinement.
The deliberately generous factor `2 * target + 3` avoids any real square
root in the estimate. -/
theorem sqrtBracket_square_error_le
    (target : TheoremSixtyTwo.PositiveSquareClassRepresentative)
    (scale : Nat) (bracket : SqrtBracket target scale) :
    bracket.upper ^ 2 - target.representative.value ≤
      (2 * target.representative.value + 3) /
        (scale + 1 : Nat) := by
  let refinement : Nat := scale + 1
  have refinementPositiveNatural : 0 < refinement := by
    unfold refinement
    omega0
  have refinementPositive : (0 : Scalar) < (refinement : Scalar) :=
    RFAP.ConstructiveFraction.natCast_pos_direct
      refinementPositiveNatural
  have refinementAtLeastOneNatural : 1 ≤ refinement := by
    unfold refinement
    omega0
  have refinementAtLeastOne : (1 : Scalar) ≤ (refinement : Scalar) := by
    simpa only [Nat.cast_one] using
      RFAP.ConstructiveFraction.natCast_le_direct
        refinementAtLeastOneNatural
  have denominatorAtLeastRefinementNatural :
      refinement ≤ bracket.denominator := by
    rw [bracket.denominator_eq]
    have denominatorAtLeastOne : 1 ≤ target.denominator :=
      target.denominator_positive
    calc
      refinement = 1 * refinement := by omega0
      _ ≤ target.denominator * refinement :=
        Nat.mul_le_mul_right refinement denominatorAtLeastOne
  have denominatorAtLeastRefinement :
      (refinement : Scalar) ≤ (bracket.denominator : Scalar) :=
    RFAP.ConstructiveFraction.natCast_le_direct
      denominatorAtLeastRefinementNatural
  have denominatorPositive :
      (0 : Scalar) < (bracket.denominator : Scalar) :=
    RFAP.ConstructiveFraction.natCast_pos_direct
      bracket.denominator_positive
  have widthPositive : 0 < bracket.upper - bracket.lower := by
    rw [bracket.width_eq]
    exact RFAP.ConstructiveFraction.div_pos_direct (by decide)
      denominatorPositive
  have widthLeRefinement :
      bracket.upper - bracket.lower ≤ 1 / (refinement : Scalar) := by
    rw [bracket.width_eq]
    exact RFAP.ConstructiveFraction.div_le_div_of_nonneg_left_direct
      (by decide) refinementPositive denominatorAtLeastRefinement
  have widthLeOne : bracket.upper - bracket.lower ≤ 1 := by
    calc
      bracket.upper - bracket.lower ≤ 1 / (refinement : Scalar) :=
        widthLeRefinement
      _ ≤ 1 / (1 : Scalar) :=
        RFAP.ConstructiveFraction.div_le_div_of_nonneg_left_direct
          (by decide) (by decide) refinementAtLeastOne
      _ = 1 := by decide
  have valueLeSquareSuccessor : target.representative.value ≤
      (target.representative.value + 1) ^ 2 := by
    have extraNonnegative : 0 ≤
        target.representative.value ^ 2 +
          target.representative.value + 1 :=
      add_nonneg
        (add_nonneg
          (RFAP.ConstructiveFraction.sq_nonneg_direct
            target.representative.value)
          target.positive.le)
        (by decide)
    calc
      target.representative.value =
          target.representative.value + 0 := by ring1
      _ ≤ target.representative.value +
          (target.representative.value ^ 2 +
            target.representative.value + 1) :=
        (by
          simpa only [zero_add, add_comm] using
            RFAP.ConstructiveFraction.add_le_add_right_direct
              extraNonnegative target.representative.value)
      _ = (target.representative.value + 1) ^ 2 := by ring1
  have lowerLeSuccessor : bracket.lower ≤
      target.representative.value + 1 := by
    apply RFAP.ConstructiveFraction.le_of_sq_le_sq_direct
      (add_nonneg target.positive.le (by decide))
    exact bracket.lower_square_le.trans valueLeSquareSuccessor
  have twiceLowerLe : 2 * bracket.lower ≤
      2 * (target.representative.value + 1) :=
    RFAP.ConstructiveFraction.mul_le_mul_of_nonneg_left_direct
      lowerLeSuccessor (by decide)
  have sumLe : bracket.upper + bracket.lower ≤
      2 * target.representative.value + 3 := by
    calc
      bracket.upper + bracket.lower =
          2 * bracket.lower + (bracket.upper - bracket.lower) := by ring1
      _ ≤ 2 * (target.representative.value + 1) + 1 :=
        RFAP.ConstructiveFraction.add_le_add_direct twiceLowerLe widthLeOne
      _ = 2 * target.representative.value + 3 := by ring1
  have sumNonnegative : 0 ≤ bracket.upper + bracket.lower :=
    add_nonneg bracket.upper_positive.le bracket.lower_nonnegative
  have reciprocalNonnegative :
      0 ≤ 1 / (refinement : Scalar) :=
    (RFAP.ConstructiveFraction.div_pos_direct (by decide)
      refinementPositive).le
  calc
    bracket.upper ^ 2 - target.representative.value ≤
        bracket.upper ^ 2 - bracket.lower ^ 2 :=
      RFAP.ConstructiveFraction.sub_le_sub_left_direct
        bracket.lower_square_le (bracket.upper ^ 2)
    _ = (bracket.upper - bracket.lower) *
        (bracket.upper + bracket.lower) := by ring1
    _ ≤ (1 / (refinement : Scalar)) *
        (2 * target.representative.value + 3) :=
      RFAP.ConstructiveFraction.mul_le_mul_direct widthLeRefinement sumLe
        sumNonnegative reciprocalNonnegative
    _ = (2 * target.representative.value + 3) /
        (scale + 1 : Nat) := by
      unfold refinement
      simp only [RFAP.ExplicitField.div_eq_mul_inv]
      ring1

/-! ## A rational norm-one stereographic candidate -/

/-- Select the projectively equal sign whose scalar coordinate is
nonnegative. -/
def orientNonnegative (proportion : NonNullProportion Scalar) :
    NonNullProportion Scalar :=
  if nonnegative : 0 ≤ proportion.scalar then proportion
  else NonNullProportion.scale (-1) (by
    intro negativeOneZero
    have oneZero : (1 : Scalar) = 0 := by
      calc
        1 = -(-1 : Scalar) := by ring1
        _ = -0 := by rw [negativeOneZero]
        _ = 0 := by ring1
    exact proportion.one_ne_zero oneZero) proportion

theorem orientNonnegative_equivalent (proportion : NonNullProportion Scalar) :
    proportion.Equivalent (orientNonnegative proportion) := by
  unfold orientNonnegative
  split
  · exact NonNullProportion.equivalent_refl proportion
  · rename_i negative
    refine ⟨-1, ?_, rfl⟩
    intro negativeOneZero
    have oneZero : (1 : Scalar) = 0 := by
      calc
        1 = -(-1 : Scalar) := by ring1
        _ = -0 := by rw [negativeOneZero]
        _ = 0 := by ring1
    exact proportion.one_ne_zero oneZero

theorem orientNonnegative_scalar_nonnegative
    (proportion : NonNullProportion Scalar) :
    0 ≤ (orientNonnegative proportion).scalar := by
  unfold orientNonnegative
  split
  · assumption
  · rename_i negative
    have scaledScalar :
        (Proportion.scale (-1) proportion.toProportion).scalar =
          -proportion.scalar := by
      change (-1 : Scalar) * proportion.scalar = -proportion.scalar
      ring1
    change 0 ≤ (Proportion.scale (-1) proportion.toProportion).scalar
    rw [scaledScalar]
    have less := RFAP.ConstructiveFraction.lt_of_not_ge_direct negative
    exact (neg_pos.mpr less).le

theorem orientNonnegative_norm
    (proportion : NonNullProportion Scalar) :
    (orientNonnegative proportion).toProportion.norm =
      proportion.toProportion.norm := by
  unfold orientNonnegative
  split
  · rfl
  · change (Proportion.scale (-1) proportion.toProportion).norm =
      proportion.toProportion.norm
    rw [Proportion.norm_scale]
    ring1

/-- Positive norm packaged for the finite square-root bracket. -/
def positiveNormTarget (proportion : NonNullProportion Scalar) :
    TheoremSixtyTwo.PositiveSquareClassRepresentative where
  representative := proportion.quadranceClass
  positive := TheoremSixtyTwo.nonNullProportion_norm_positive proportion

/-- Unnormalized rational stereographic point. -/
def stereographicRaw (proportion : NonNullProportion Scalar)
    (root : Scalar) : Proportion Scalar :=
  let chart := root + proportion.scalar
  { scalar := chart ^ 2 - proportion.vector.quadrance
    vector := Vector.scale (2 * chart) proportion.vector }

/-- Common stereographic denominator. -/
def stereographicDenominator (proportion : NonNullProportion Scalar)
    (root : Scalar) : Scalar :=
  let chart := root + proportion.scalar
  chart ^ 2 + proportion.vector.quadrance

theorem stereographicRaw_norm
    (proportion : NonNullProportion Scalar) (root : Scalar) :
    (stereographicRaw proportion root).norm =
      stereographicDenominator proportion root ^ 2 := by
  unfold stereographicRaw stereographicDenominator Proportion.norm
  rw [Vector.quadrance_scale]
  ring1

theorem vector_quadrance_nonnegative (vector : Vector Scalar) :
    0 ≤ vector.quadrance := by
  unfold Vector.quadrance Vector.dot
  exact add_nonneg
    (add_nonneg
      (by simpa only [pow_two] using
        RFAP.ConstructiveFraction.sq_nonneg_direct vector.t)
      (by simpa only [pow_two] using
        RFAP.ConstructiveFraction.sq_nonneg_direct vector.r))
    (by simpa only [pow_two] using
      RFAP.ConstructiveFraction.sq_nonneg_direct vector.s)

theorem stereographicDenominator_positive
    (proportion : NonNullProportion Scalar) (root : Scalar)
    (rootPositive : 0 < root) (scalarNonnegative : 0 ≤ proportion.scalar) :
    0 < stereographicDenominator proportion root := by
  have chartPositive : 0 < root + proportion.scalar :=
    add_pos_of_pos_of_nonneg rootPositive scalarNonnegative
  have chartSquarePositive :=
    RFAP.ConstructiveFraction.pow_pos_direct chartPositive 2
  unfold stereographicDenominator
  exact add_pos_of_pos_of_nonneg chartSquarePositive
    (vector_quadrance_nonnegative proportion.vector)

/-- Cached finite data for one exact unit-quaternion candidate. -/
structure UnitCandidate (source : NonNullProportion Scalar) (scale : Nat) where
  oriented : NonNullProportion Scalar
  oriented_eq : oriented = orientNonnegative source
  oriented_equivalent : source.Equivalent oriented
  bracket : SqrtBracket (positiveNormTarget source) scale
  root : Scalar
  root_eq : root = bracket.upper
  root_positive : 0 < root
  raw : NonNullProportion Scalar
  raw_value : raw.toProportion = stereographicRaw oriented root
  denominator : Scalar
  denominator_eq : denominator = stereographicDenominator oriented root
  denominator_positive : 0 < denominator
  unit : NonNullProportion Scalar
  unit_eq : unit = NonNullProportion.scale denominator⁻¹
    (RFAP.ExplicitField.inv_ne_zero denominator_positive.ne') raw
  unit_norm : unit.toProportion.norm = 1
  unit_equivalent_raw : raw.Equivalent unit
  unit_hasUnitRepresentative : unit.HasUnitRepresentative

/-- Compute one rational norm-one candidate at the supplied finite square-root
refinement. -/
def unitCandidate (source : NonNullProportion Scalar) (scale : Nat) :
    UnitCandidate source scale := by
  let oriented := orientNonnegative source
  let bracket := sqrtBracket (positiveNormTarget source) scale
  let root := bracket.upper
  have rootPositive : 0 < root := bracket.upper_positive
  have scalarNonnegative : 0 ≤ oriented.scalar :=
    orientNonnegative_scalar_nonnegative source
  let denominator := stereographicDenominator oriented root
  have denominatorPositive : 0 < denominator :=
    stereographicDenominator_positive oriented root rootPositive
      scalarNonnegative
  let raw : NonNullProportion Scalar :=
    { toProportion := stereographicRaw oriented root
      normNonzero := by
        rw [stereographicRaw_norm]
        simpa only [pow_two] using RFAP.ExplicitField.mul_ne_zero
          denominatorPositive.ne' denominatorPositive.ne' }
  let unit := NonNullProportion.scale denominator⁻¹
    (RFAP.ExplicitField.inv_ne_zero denominatorPositive.ne') raw
  have denominatorCancel := RFAP.ExplicitField.mul_inv_cancel
    denominator denominatorPositive.ne'
  have unitNorm : unit.toProportion.norm = 1 := by
    unfold unit
    change (Proportion.scale denominator⁻¹ raw.toProportion).norm = 1
    rw [Proportion.norm_scale]
    change denominator⁻¹ ^ 2 *
      (stereographicRaw oriented root).norm = 1
    rw [stereographicRaw_norm]
    change denominator⁻¹ ^ 2 * denominator ^ 2 = 1
    calc
      denominator⁻¹ ^ 2 * denominator ^ 2 =
          (denominator * denominator⁻¹) ^ 2 := by ring1
      _ = 1 := by rw [denominatorCancel]; ring1
  refine
    { oriented := oriented
      oriented_eq := rfl
      oriented_equivalent := orientNonnegative_equivalent source
      bracket := bracket
      root := root
      root_eq := rfl
      root_positive := rootPositive
      raw := raw
      raw_value := rfl
      denominator := denominator
      denominator_eq := rfl
      denominator_positive := denominatorPositive
      unit := unit
      unit_eq := rfl
      unit_norm := unitNorm
      unit_equivalent_raw := ?_
      unit_hasUnitRepresentative := ?_ }
  · refine ⟨denominator⁻¹,
      RFAP.ExplicitField.inv_ne_zero denominatorPositive.ne', rfl⟩
  · refine ⟨1, unit.one_ne_zero, ?_⟩
    rw [Proportion.one_scale]
    exact unitNorm

/-- The raw candidate is a scalar multiple of the oriented source plus one
explicit scalar-coordinate error `root^2 - norm`. -/
theorem stereographicRaw_decomposition
    (source : NonNullProportion Scalar) (root : Scalar) :
    stereographicRaw source root =
      { scalar :=
          (2 * (root + source.scalar)) * source.scalar +
            (root ^ 2 - source.toProportion.norm)
        vector := Vector.scale (2 * (root + source.scalar)) source.vector } := by
  apply Proportion.ext
  · unfold stereographicRaw Proportion.norm
    ring1
  · rfl

/-- Multiplying the raw candidate by the conjugate target cancels its scalar
multiple exactly; only the square-root error remains in the vector part. -/
theorem stereographicRaw_mul_conjugate_vector_quadrance
    (source : NonNullProportion Scalar) (root : Scalar) :
    (Proportion.mul (stereographicRaw source root)
        (Proportion.conjugate source.toProportion)).vector.quadrance =
      (root ^ 2 - source.toProportion.norm) ^ 2 *
        source.vector.quadrance := by
  unfold stereographicRaw Proportion.mul Proportion.conjugate Proportion.norm
    Vector.quadrance Vector.dot Vector.neg Vector.scale Vector.sub Vector.add
    Vector.cross
  ring1

/-- Exact rational error of the cached norm-one candidate.  The only
approximation term is the square-root bracket error `root² - norm`; all
remaining factors are cached source and chart data. -/
theorem unitCandidate_matrixDistanceSq
    (source : NonNullProportion Scalar) (scale : Nat) :
    matrixDistanceSq (unitCandidate source scale).unit.rotationMatrix
        source.rotationMatrix =
      8 * (((unitCandidate source scale).root ^ 2 -
          source.toProportion.norm) ^ 2 *
        (unitCandidate source scale).oriented.vector.quadrance /
        ((unitCandidate source scale).denominator ^ 2 *
          source.toProportion.norm)) := by
  let candidate := unitCandidate source scale
  have rawUnit : candidate.raw.rotationMatrix =
      candidate.unit.rotationMatrix :=
    NonNullProportion.rotationMatrix_respects_equivalent
      candidate.unit_equivalent_raw
  have sourceOriented : source.rotationMatrix =
      candidate.oriented.rotationMatrix :=
    NonNullProportion.rotationMatrix_respects_equivalent
      candidate.oriented_equivalent
  change matrixDistanceSq candidate.unit.rotationMatrix
      source.rotationMatrix =
    8 * ((candidate.root ^ 2 - source.toProportion.norm) ^ 2 *
      candidate.oriented.vector.quadrance /
      (candidate.denominator ^ 2 * source.toProportion.norm))
  rw [← rawUnit, sourceOriented,
    matrixDistanceSq_eq_eight_mul_halfSpread_relative]
  rw [NonNullProportion.halfSpread_rotation _ (by decide)]
  have vectorQuadrance :
      (NonNullProportion.mul candidate.raw
        (NonNullProportion.conjugate candidate.oriented)).vector.quadrance =
        (candidate.root ^ 2 - candidate.oriented.toProportion.norm) ^ 2 *
          candidate.oriented.vector.quadrance := by
    change (Proportion.mul candidate.raw.toProportion
      (Proportion.conjugate candidate.oriented.toProportion)).vector.quadrance =
        _
    rw [candidate.raw_value]
    exact stereographicRaw_mul_conjugate_vector_quadrance
      candidate.oriented candidate.root
  have conjugateNorm :
      (NonNullProportion.conjugate candidate.oriented).toProportion.norm =
        candidate.oriented.toProportion.norm := by
    change (Proportion.conjugate candidate.oriented.toProportion).norm = _
    exact Proportion.norm_conjugate candidate.oriented.toProportion
  have rawNorm : candidate.raw.toProportion.norm =
      candidate.denominator ^ 2 := by
    rw [candidate.raw_value, stereographicRaw_norm,
      ← candidate.denominator_eq]
  have orientedNorm : candidate.oriented.toProportion.norm =
      source.toProportion.norm := by
    rw [candidate.oriented_eq]
    exact orientNonnegative_norm source
  rw [vectorQuadrance, NonNullProportion.mul_norm, conjugateNorm, rawNorm,
    orientedNorm]

/-- The bracket error of a cached candidate is strictly positive. -/
theorem unitCandidate_square_error_positive
    (source : NonNullProportion Scalar) (scale : Nat) :
    0 < (unitCandidate source scale).root ^ 2 -
      source.toProportion.norm := by
  let candidate := unitCandidate source scale
  have upperBound := candidate.bracket.value_lt_upper_square
  change source.toProportion.norm < candidate.bracket.upper ^ 2 at upperBound
  rw [← candidate.root_eq] at upperBound
  exact RFAP.ConstructiveFraction.sub_pos_direct upperBound

/-- The candidate's square-root error obeys the reciprocal finite-refinement
bound supplied by its cached bracket. -/
theorem unitCandidate_square_error_le
    (source : NonNullProportion Scalar) (scale : Nat) :
    (unitCandidate source scale).root ^ 2 -
        source.toProportion.norm ≤
      (2 * source.toProportion.norm + 3) / (scale + 1 : Nat) := by
  let candidate := unitCandidate source scale
  have bounded := sqrtBracket_square_error_le
    (positiveNormTarget source) scale candidate.bracket
  change candidate.bracket.upper ^ 2 - source.toProportion.norm ≤ _ at bounded
  rw [← candidate.root_eq] at bounded
  exact bounded

/-- The oriented vector quadrance is bounded by the positive source norm. -/
theorem unitCandidate_oriented_vector_quadrance_le_norm
    (source : NonNullProportion Scalar) (scale : Nat) :
    (unitCandidate source scale).oriented.vector.quadrance ≤
      source.toProportion.norm := by
  let candidate := unitCandidate source scale
  have scalarSquareNonnegative :=
    RFAP.ConstructiveFraction.sq_nonneg_direct candidate.oriented.scalar
  have bounded : candidate.oriented.vector.quadrance ≤
      candidate.oriented.toProportion.norm := by
    unfold Proportion.norm
    exact le_add_of_nonneg_left scalarSquareNonnegative
  rw [candidate.oriented_eq, orientNonnegative_norm source] at bounded
  exact bounded

/-- The positive stereographic denominator strictly exceeds the source
norm, providing the denominator separation used by the error estimate. -/
theorem unitCandidate_norm_lt_denominator
    (source : NonNullProportion Scalar) (scale : Nat) :
    source.toProportion.norm < (unitCandidate source scale).denominator := by
  let candidate := unitCandidate source scale
  have rootSquareAbove := candidate.bracket.value_lt_upper_square
  change source.toProportion.norm < candidate.bracket.upper ^ 2 at rootSquareAbove
  rw [← candidate.root_eq] at rootSquareAbove
  have scalarNonnegative : 0 ≤ candidate.oriented.scalar := by
    rw [candidate.oriented_eq]
    exact orientNonnegative_scalar_nonnegative source
  have rootLeChart : candidate.root ≤
      candidate.root + candidate.oriented.scalar :=
    le_add_of_nonneg_right scalarNonnegative
  have chartSquareAbove : candidate.root ^ 2 ≤
      (candidate.root + candidate.oriented.scalar) ^ 2 :=
    RFAP.ConstructiveFraction.pow_le_pow_direct
      candidate.root_positive.le rootLeChart 2
  have vectorNonnegative :=
    vector_quadrance_nonnegative candidate.oriented.vector
  calc
    source.toProportion.norm < candidate.root ^ 2 := rootSquareAbove
    _ ≤ (candidate.root + candidate.oriented.scalar) ^ 2 :=
      chartSquareAbove
    _ ≤ (candidate.root + candidate.oriented.scalar) ^ 2 +
        candidate.oriented.vector.quadrance :=
      le_add_of_nonneg_right vectorNonnegative
    _ = candidate.denominator := by
      rw [candidate.denominator_eq]
      rfl

/-- Conservative rational refinement demand for one positive squared-radius
request.  Its natural numerator is already a terminating sufficient scale. -/
def precisionDemand (source : NonNullProportion Scalar)
    (radiusSq : Scalar) : Scalar :=
  8 * (2 * source.toProportion.norm + 3) ^ 2 /
    (radiusSq * source.toProportion.norm ^ 2)

theorem precisionDemand_positive (source : NonNullProportion Scalar)
    (radiusSq : Scalar) (radiusPositive : 0 < radiusSq) :
    0 < precisionDemand source radiusSq := by
  have normPositive :=
    TheoremSixtyTwo.nonNullProportion_norm_positive source
  have factorPositive : 0 < 2 * source.toProportion.norm + 3 := by
    exact add_pos
      (RFAP.ConstructiveFraction.mul_pos_direct (by decide) normPositive)
      (by decide)
  unfold precisionDemand
  exact RFAP.ConstructiveFraction.div_pos_direct
    (RFAP.ConstructiveFraction.mul_pos_direct (by decide)
      (RFAP.ConstructiveFraction.pow_pos_direct factorPositive 2))
    (RFAP.ConstructiveFraction.mul_pos_direct radiusPositive
      (RFAP.ConstructiveFraction.pow_pos_direct normPositive 2))

/-- A finite refinement selected directly from the canonical numerator of
the conservative rational demand. -/
def precisionScale (source : NonNullProportion Scalar)
    (radiusSq : Scalar) : Nat :=
  (precisionDemand source radiusSq).num.toNat

theorem precisionDemand_lt_precisionScale_succ
    (source : NonNullProportion Scalar) (radiusSq : Scalar)
    (radiusPositive : 0 < radiusSq) :
    precisionDemand source radiusSq <
      (precisionScale source radiusSq + 1 : Nat) := by
  exact positiveRational_lt_numerator_succ
    (precisionDemand source radiusSq)
    (precisionDemand_positive source radiusSq radiusPositive)

/-- Any refinement strictly above the conservative demand meets the requested
squared matrix radius.  The proof clears only positive rational factors and
uses the cached bracket, chart, and norm data. -/
theorem unitCandidate_matrixDistanceSq_lt_of_demand_lt
    (source : NonNullProportion Scalar) (radiusSq : Scalar)
    (radiusPositive : 0 < radiusSq) (scale : Nat)
    (demandBelow : precisionDemand source radiusSq <
      (scale + 1 : Nat)) :
    matrixDistanceSq (unitCandidate source scale).unit.rotationMatrix
        source.rotationMatrix < radiusSq := by
  let candidate := unitCandidate source scale
  let norm := source.toProportion.norm
  let error := candidate.root ^ 2 - norm
  let factor := 2 * norm + 3
  let refinement : Scalar := (scale + 1 : Nat)
  have normPositive : 0 < norm := by
    unfold norm
    exact TheoremSixtyTwo.nonNullProportion_norm_positive source
  have radiusNormSquarePositive : 0 < radiusSq * norm ^ 2 :=
    RFAP.ConstructiveFraction.mul_pos_direct radiusPositive
      (RFAP.ConstructiveFraction.pow_pos_direct normPositive 2)
  have factorPositive : 0 < factor := by
    unfold factor
    exact add_pos
      (RFAP.ConstructiveFraction.mul_pos_direct (by decide) normPositive)
      (by decide)
  have refinementPositive : 0 < refinement := by
    unfold refinement
    exact RFAP.ConstructiveFraction.natCast_pos_direct (by omega0)
  have refinementAtLeastOne : (1 : Scalar) ≤ refinement := by
    unfold refinement
    simpa only [Nat.cast_one] using
      RFAP.ConstructiveFraction.natCast_le_direct (by omega0 : 1 ≤ scale + 1)
  have refinementLeSquare : refinement ≤ refinement ^ 2 := by
    calc
      refinement = 1 * refinement := by ring1
      _ ≤ refinement * refinement :=
        RFAP.ConstructiveFraction.mul_le_mul_of_nonneg_right_direct
          refinementAtLeastOne refinementPositive.le
      _ = refinement ^ 2 := by ring1
  have errorPositive : 0 < error := by
    unfold error norm candidate
    exact unitCandidate_square_error_positive source scale
  have errorLe : error ≤ factor / refinement := by
    unfold error factor norm refinement candidate
    exact unitCandidate_square_error_le source scale
  have errorTimesRefinementLe : error * refinement ≤ factor :=
    (RFAP.ConstructiveFraction.le_div_iff_pos refinementPositive).mp errorLe
  have errorTimesRefinementNonnegative :
      0 ≤ error * refinement :=
    RFAP.ConstructiveFraction.mul_nonneg_direct errorPositive.le
      refinementPositive.le
  have errorSquareCleared :
      error ^ 2 * refinement ^ 2 ≤ factor ^ 2 := by
    have squares := RFAP.ConstructiveFraction.pow_le_pow_direct
      errorTimesRefinementNonnegative errorTimesRefinementLe 2
    calc
      error ^ 2 * refinement ^ 2 =
          (error * refinement) ^ 2 := by ring1
      _ ≤ factor ^ 2 := squares
  have demandBelowSquare : precisionDemand source radiusSq <
      refinement ^ 2 := by
    exact demandBelow.trans_le refinementLeSquare
  have demandCleared : 8 * factor ^ 2 <
      refinement ^ 2 * (radiusSq * norm ^ 2) := by
    apply (RFAP.ConstructiveFraction.div_lt_iff_pos
      radiusNormSquarePositive).mp
    change precisionDemand source radiusSq < refinement ^ 2
    exact demandBelowSquare
  have errorCoefficientNonnegative : 0 ≤ 8 * norm :=
    RFAP.ConstructiveFraction.mul_nonneg_direct (by decide) normPositive.le
  have scaledErrorLe :
      (8 * error ^ 2 * norm) * refinement ^ 2 ≤
        8 * factor ^ 2 * norm := by
    calc
      (8 * error ^ 2 * norm) * refinement ^ 2 =
          (8 * norm) * (error ^ 2 * refinement ^ 2) := by ring1
      _ ≤ (8 * norm) * factor ^ 2 :=
        RFAP.ConstructiveFraction.mul_le_mul_of_nonneg_left_direct
          errorSquareCleared errorCoefficientNonnegative
      _ = 8 * factor ^ 2 * norm := by ring1
  have demandTimesNorm :
      8 * factor ^ 2 * norm <
        (radiusSq * norm ^ 2 * norm) * refinement ^ 2 := by
    have scaled :=
      RFAP.ConstructiveFraction.mul_lt_mul_of_pos_right_direct
        demandCleared normPositive
    calc
      8 * factor ^ 2 * norm <
          (refinement ^ 2 * (radiusSq * norm ^ 2)) * norm := scaled
      _ = (radiusSq * norm ^ 2 * norm) * refinement ^ 2 := by ring1
  have coreScaled :
      (8 * error ^ 2 * norm) * refinement ^ 2 <
        (radiusSq * norm ^ 2 * norm) * refinement ^ 2 :=
    scaledErrorLe.trans_lt demandTimesNorm
  have core : 8 * error ^ 2 * norm <
      radiusSq * norm ^ 2 * norm :=
    RFAP.ConstructiveFraction.lt_of_mul_lt_mul_right_direct coreScaled
      (RFAP.ConstructiveFraction.pow_pos_direct refinementPositive 2)
  have vectorNonnegative :
      0 ≤ candidate.oriented.vector.quadrance :=
    vector_quadrance_nonnegative candidate.oriented.vector
  have vectorLeNorm : candidate.oriented.vector.quadrance ≤ norm := by
    unfold candidate norm
    exact unitCandidate_oriented_vector_quadrance_le_norm source scale
  have numeratorLe :
      8 * error ^ 2 * candidate.oriented.vector.quadrance ≤
        8 * error ^ 2 * norm := by
    exact RFAP.ConstructiveFraction.mul_le_mul_of_nonneg_left_direct
      vectorLeNorm
      (RFAP.ConstructiveFraction.mul_nonneg_direct (by decide)
        (RFAP.ConstructiveFraction.sq_nonneg_direct error))
  have normBelowDenominator : norm < candidate.denominator := by
    unfold norm candidate
    exact unitCandidate_norm_lt_denominator source scale
  have normSquareLeDenominatorSquare :
      norm ^ 2 ≤ candidate.denominator ^ 2 :=
    RFAP.ConstructiveFraction.pow_le_pow_direct normPositive.le
      normBelowDenominator.le 2
  have radiusNormNonnegative : 0 ≤ radiusSq * norm :=
    RFAP.ConstructiveFraction.mul_nonneg_direct radiusPositive.le
      normPositive.le
  have requestedDenominatorLe : radiusSq * norm ^ 2 * norm ≤
      radiusSq * candidate.denominator ^ 2 * norm := by
    calc
      radiusSq * norm ^ 2 * norm =
          (radiusSq * norm) * norm ^ 2 := by ring1
      _ ≤ (radiusSq * norm) * candidate.denominator ^ 2 :=
        RFAP.ConstructiveFraction.mul_le_mul_of_nonneg_left_direct
          normSquareLeDenominatorSquare radiusNormNonnegative
      _ = radiusSq * candidate.denominator ^ 2 * norm := by ring1
  have numeratorStrict :
      8 * error ^ 2 * candidate.oriented.vector.quadrance <
        radiusSq * (candidate.denominator ^ 2 * norm) := by
    calc
      8 * error ^ 2 * candidate.oriented.vector.quadrance ≤
          8 * error ^ 2 * norm := numeratorLe
      _ < radiusSq * norm ^ 2 * norm := core
      _ ≤ radiusSq * candidate.denominator ^ 2 * norm :=
        requestedDenominatorLe
      _ = radiusSq * (candidate.denominator ^ 2 * norm) := by ring1
  have denominatorPositive : 0 < candidate.denominator ^ 2 * norm :=
    RFAP.ConstructiveFraction.mul_pos_direct
      (RFAP.ConstructiveFraction.pow_pos_direct
        candidate.denominator_positive 2)
      normPositive
  change matrixDistanceSq candidate.unit.rotationMatrix
      source.rotationMatrix < radiusSq
  rw [unitCandidate_matrixDistanceSq]
  change 8 * (error ^ 2 * candidate.oriented.vector.quadrance /
      (candidate.denominator ^ 2 * norm)) < radiusSq
  rw [show 8 * (error ^ 2 * candidate.oriented.vector.quadrance /
      (candidate.denominator ^ 2 * norm)) =
      (8 * error ^ 2 * candidate.oriented.vector.quadrance) /
        (candidate.denominator ^ 2 * norm) by
    simp only [RFAP.ExplicitField.div_eq_mul_inv]
    ring1]
  exact (RFAP.ConstructiveFraction.div_lt_iff_pos denominatorPositive).2
    numeratorStrict

/-! ## One finite certificate for one rational precision request -/

/-- The complete finite output for one target rotation and one positive
rational squared radius.  The canonical source representative, selected
refinement, bracketed candidate, exact unit representative, associated
rotation, and final error comparison are all retained as executable data. -/
structure KernelApproximationCertificate (target : Rotation Scalar)
    (radiusSq : Scalar) where
  radius_positive : 0 < radiusSq
  source : NonNullProportion Scalar
  source_eq : source = RotationProportion.ofRotation target (by decide)
  source_represents : source.rotationMatrix = target.matrix
  scale : Nat
  scale_eq : scale = precisionScale source radiusSq
  candidate : UnitCandidate source scale
  candidate_eq : candidate = unitCandidate source scale
  approximant : NonNullProportion Scalar
  approximant_eq : approximant = candidate.unit
  approximant_norm : approximant.toProportion.norm = 1
  approximant_hasUnitRepresentative : approximant.HasUnitRepresentative
  rotation : Rotation Scalar
  rotation_eq : rotation = approximant.rotation
  error_lt : matrixDistanceSq rotation.matrix target.matrix < radiusSq

/-- Compute an exact rational unit-kernel approximation for one displayed
rational rotation and one positive rational squared-radius request.  The
constructor performs only the canonical finite inverse, base-four
integer square-root refinement, and fixed-coordinate rational arithmetic. -/
def kernelApproximation (target : Rotation Scalar) (radiusSq : Scalar)
    (radiusPositive : 0 < radiusSq) :
    KernelApproximationCertificate target radiusSq := by
  let source := RotationProportion.ofRotation target (by decide)
  have sourceRepresents : source.rotationMatrix = target.matrix :=
    RotationProportion.ofRotation_rotationMatrix target (by decide)
  let scale := precisionScale source radiusSq
  let candidate := unitCandidate source scale
  have demandBelow : precisionDemand source radiusSq <
      (scale + 1 : Nat) := by
    unfold scale
    exact precisionDemand_lt_precisionScale_succ source radiusSq
      radiusPositive
  have sourceError :
      matrixDistanceSq candidate.unit.rotationMatrix source.rotationMatrix <
        radiusSq := by
    unfold candidate
    exact unitCandidate_matrixDistanceSq_lt_of_demand_lt source radiusSq
      radiusPositive scale demandBelow
  have targetError :
      matrixDistanceSq candidate.unit.rotationMatrix target.matrix <
        radiusSq := by
    rw [← sourceRepresents]
    exact sourceError
  exact
    { radius_positive := radiusPositive
      source := source
      source_eq := rfl
      source_represents := sourceRepresents
      scale := scale
      scale_eq := rfl
      candidate := candidate
      candidate_eq := rfl
      approximant := candidate.unit
      approximant_eq := rfl
      approximant_norm := candidate.unit_norm
      approximant_hasUnitRepresentative :=
        candidate.unit_hasUnitRepresentative
      rotation := candidate.unit.rotation
      rotation_eq := rfl
      error_lt := targetError }

/-- The candidate's stored rotation is in the unit-quaternion kernel. -/
theorem unitCandidate_rotation_hasUnitQuaternion
    (source : NonNullProportion Scalar) (scale : Nat) :
    (unitCandidate source scale).unit.HasUnitRepresentative :=
  (unitCandidate source scale).unit_hasUnitRepresentative

end FiniteKernelApproximation

end RationalRotations
