import mathlib.Tactic.QuotientFreeRing
import CCL.Boundary.Curve.Rational
import RFAP.Sturm.RootCount
import RFAP.Geometry.Boxes

/-!
# Finite box conditions along a rational curve

A rational curve is stored homogeneously as `N(t) / D(t)`.  On every
displayed parameter where `D(t)` is nonzero, membership of the affine point
in a rational box is equivalent to four nonnegative univariate polynomial
evaluations.  The common positive factor is the explicitly displayed
quadrance `normSq (D(t))`, so no denominator sign choice or square root is
needed.

The nonzero members of the four-polynomial family are also collected into a
single finite product guard.  A later common Sturm subdivision can therefore
cut once while preserving all box-edge signs; identically-zero edge
conditions remain explicit instead of making the guard vanish.
-/

namespace CCL.CurveBoxConditions

abbrev Coordinate := RFAP.ConstructiveFraction.Rational
abbrev Gaussian := RFAP.ConstructiveGaussian.Gaussian
abbrev Box := RFAP.Boxes.Box
abbrev RationalCurve := CCL.RationalCurve.RationalCurve
abbrev CoordinatePolynomial :=
  RFAP.ComputablePolynomial.DensePolynomial Coordinate

open RFAP.ConstructiveGaussian.Gaussian
open RFAP.ComputablePolynomial.DensePolynomial

def numeratorReal (curve : RationalCurve) : CoordinatePolynomial :=
  RFAP.PathPolynomial.realPart curve.numerator

def numeratorImaginary (curve : RationalCurve) : CoordinatePolynomial :=
  RFAP.PathPolynomial.imagPart curve.numerator

def denominatorReal (curve : RationalCurve) : CoordinatePolynomial :=
  RFAP.PathPolynomial.realPart curve.denominator

def denominatorImaginary (curve : RationalCurve) : CoordinatePolynomial :=
  RFAP.PathPolynomial.imagPart curve.denominator

/-- Polynomial quadrance of the homogeneous denominator. -/
def denominatorNormSq (curve : RationalCurve) : CoordinatePolynomial :=
  denominatorReal curve * denominatorReal curve +
    denominatorImaginary curve * denominatorImaginary curve

/-- Numerator of the real coordinate after multiplying by `conj D`. -/
def affineRealNumerator (curve : RationalCurve) : CoordinatePolynomial :=
  numeratorReal curve * denominatorReal curve +
    numeratorImaginary curve * denominatorImaginary curve

/-- Numerator of the imaginary coordinate after multiplying by `conj D`. -/
def affineImaginaryNumerator (curve : RationalCurve) : CoordinatePolynomial :=
  numeratorImaginary curve * denominatorReal curve -
    numeratorReal curve * denominatorImaginary curve

def xLowerPolynomial (curve : RationalCurve) (box : Box) :
    CoordinatePolynomial :=
  affineRealNumerator curve - scale box.xLower (denominatorNormSq curve)

def xUpperPolynomial (curve : RationalCurve) (box : Box) :
    CoordinatePolynomial :=
  scale box.xUpper (denominatorNormSq curve) - affineRealNumerator curve

def yLowerPolynomial (curve : RationalCurve) (box : Box) :
    CoordinatePolynomial :=
  affineImaginaryNumerator curve - scale box.yLower (denominatorNormSq curve)

def yUpperPolynomial (curve : RationalCurve) (box : Box) :
    CoordinatePolynomial :=
  scale box.yUpper (denominatorNormSq curve) -
    affineImaginaryNumerator curve

/-- The exact four finite polynomials whose weak signs express closed-box
membership along the curve. -/
def conditionPolynomials (curve : RationalCurve) (box : Box) :
    List CoordinatePolynomial :=
  [xLowerPolynomial curve box, xUpperPolynomial curve box,
    yLowerPolynomial curve box, yUpperPolynomial curve box]

/-- Conditions used by the event-profile layer.  The homogeneous denominator
quadrance is retained in front of the four affine box edges so every final
profile is explicitly classified as a pole factor or uniformly apart from
the pole polynomial. -/
def profiledConditionPolynomials (curve : RationalCurve) (box : Box) :
    List CoordinatePolynomial :=
  denominatorNormSq curve :: conditionPolynomials curve box

def Holds (curve : RationalCurve) (box : Box) (parameter : Coordinate) : Prop :=
  0 <= (xLowerPolynomial curve box).eval parameter /\
    0 <= (xUpperPolynomial curve box).eval parameter /\
    0 <= (yLowerPolynomial curve box).eval parameter /\
    0 <= (yUpperPolynomial curve box).eval parameter

def StrictHolds
    (curve : RationalCurve) (box : Box) (parameter : Coordinate) : Prop :=
  0 < (xLowerPolynomial curve box).eval parameter /\
    0 < (xUpperPolynomial curve box).eval parameter /\
    0 < (yLowerPolynomial curve box).eval parameter /\
    0 < (yUpperPolynomial curve box).eval parameter

/-- List-shaped form of the four weak box conditions.  This is convenient
for finite profile scans while remaining exactly the bundled predicate. -/
def ListedHolds
    (curve : RationalCurve) (box : Box) (parameter : Coordinate) : Prop :=
  (conditionPolynomials curve box).Forall fun condition =>
    0 ≤ condition.eval parameter

/-- List-shaped nonnegativity of the denominator quadrance followed by all
four box conditions. -/
def ProfiledListedHolds
    (curve : RationalCurve) (box : Box) (parameter : Coordinate) : Prop :=
  (profiledConditionPolynomials curve box).Forall fun condition =>
    0 ≤ condition.eval parameter

theorem listedHolds_iff_holds
    (curve : RationalCurve) (box : Box) (parameter : Coordinate) :
    ListedHolds curve box parameter ↔ Holds curve box parameter := by
  rfl

@[simp] theorem eval_denominatorNormSq
    (curve : RationalCurve) (parameter : Coordinate) :
    (denominatorNormSq curve).eval parameter =
      normSq (curve.denominatorAt parameter) := by
  simp only [denominatorNormSq, denominatorReal, denominatorImaginary,
    eval_add, eval_mul, RFAP.PathPolynomial.eval_realPart,
    RFAP.PathPolynomial.eval_imagPart,
    CCL.RationalCurve.RationalCurve.denominatorAt, normSq]
  ring1

/-- The added denominator condition imposes no affine sign assumption: its
evaluation is a Gaussian quadrance and is therefore always nonnegative. -/
theorem profiledListedHolds_iff_listedHolds
    (curve : RationalCurve) (box : Box) (parameter : Coordinate) :
    ProfiledListedHolds curve box parameter ↔
      ListedHolds curve box parameter := by
  simp only [ProfiledListedHolds, profiledConditionPolynomials,
    List.forall_cons, ListedHolds, eval_denominatorNormSq,
    RFAP.ConstructiveGaussian.Gaussian.normSq_nonneg, true_and]

@[simp] theorem eval_affineRealNumerator
    (curve : RationalCurve) (parameter : Coordinate) :
    (affineRealNumerator curve).eval parameter =
      (curve.numeratorAt parameter *
        RFAP.ConstructiveGaussian.Gaussian.conj
          (curve.denominatorAt parameter)).re := by
  simp only [affineRealNumerator, numeratorReal, numeratorImaginary,
    denominatorReal, denominatorImaginary, eval_add, eval_mul,
    RFAP.PathPolynomial.eval_realPart,
    RFAP.PathPolynomial.eval_imagPart,
    CCL.RationalCurve.RationalCurve.numeratorAt,
    CCL.RationalCurve.RationalCurve.denominatorAt,
    RFAP.ConstructiveGaussian.Gaussian.mul_re,
    RFAP.ConstructiveGaussian.Gaussian.conj]
  ring1

@[simp] theorem eval_affineImaginaryNumerator
    (curve : RationalCurve) (parameter : Coordinate) :
    (affineImaginaryNumerator curve).eval parameter =
      (curve.numeratorAt parameter *
        RFAP.ConstructiveGaussian.Gaussian.conj
          (curve.denominatorAt parameter)).im := by
  simp only [affineImaginaryNumerator, numeratorReal, numeratorImaginary,
    denominatorReal, denominatorImaginary, eval_sub, eval_mul,
    RFAP.PathPolynomial.eval_realPart,
    RFAP.PathPolynomial.eval_imagPart,
    CCL.RationalCurve.RationalCurve.numeratorAt,
    CCL.RationalCurve.RationalCurve.denominatorAt,
    RFAP.ConstructiveGaussian.Gaussian.mul_im,
    RFAP.ConstructiveGaussian.Gaussian.conj]
  ring1

theorem eval_affineRealNumerator_eq_point_mul_normSq
    (curve : RationalCurve) (parameter : Coordinate)
    (denominatorNonzero : curve.denominatorAt parameter ≠ 0) :
    (affineRealNumerator curve).eval parameter =
      (curve.point parameter).re * normSq (curve.denominatorAt parameter) := by
  have numeratorIdentity :=
    curve.numeratorAt_eq_point_mul_denominatorAt parameter denominatorNonzero
  have realIdentity :=
    congrArg RFAP.ConstructiveGaussian.Gaussian.re numeratorIdentity
  have imaginaryIdentity :=
    congrArg RFAP.ConstructiveGaussian.Gaussian.im numeratorIdentity
  rw [eval_affineRealNumerator]
  simp only [RFAP.ConstructiveGaussian.Gaussian.mul_re,
    RFAP.ConstructiveGaussian.Gaussian.mul_im,
    RFAP.ConstructiveGaussian.Gaussian.conj] at realIdentity imaginaryIdentity ⊢
  rw [realIdentity, imaginaryIdentity]
  simp only [normSq]
  ring1

theorem eval_affineImaginaryNumerator_eq_point_mul_normSq
    (curve : RationalCurve) (parameter : Coordinate)
    (denominatorNonzero : curve.denominatorAt parameter ≠ 0) :
    (affineImaginaryNumerator curve).eval parameter =
      (curve.point parameter).im * normSq (curve.denominatorAt parameter) := by
  have numeratorIdentity :=
    curve.numeratorAt_eq_point_mul_denominatorAt parameter denominatorNonzero
  have realIdentity :=
    congrArg RFAP.ConstructiveGaussian.Gaussian.re numeratorIdentity
  have imaginaryIdentity :=
    congrArg RFAP.ConstructiveGaussian.Gaussian.im numeratorIdentity
  rw [eval_affineImaginaryNumerator]
  simp only [RFAP.ConstructiveGaussian.Gaussian.mul_re,
    RFAP.ConstructiveGaussian.Gaussian.mul_im,
    RFAP.ConstructiveGaussian.Gaussian.conj] at realIdentity imaginaryIdentity ⊢
  rw [realIdentity, imaginaryIdentity]
  simp only [normSq]
  ring1

@[simp] theorem eval_xLowerPolynomial
    (curve : RationalCurve) (box : Box) (parameter : Coordinate)
    (denominatorNonzero : curve.denominatorAt parameter ≠ 0) :
    (xLowerPolynomial curve box).eval parameter =
      normSq (curve.denominatorAt parameter) *
        ((curve.point parameter).re - box.xLower) := by
  simp only [xLowerPolynomial, eval_sub, eval_scale,
    eval_affineRealNumerator_eq_point_mul_normSq curve parameter
      denominatorNonzero,
    eval_denominatorNormSq]
  ring1

@[simp] theorem eval_xUpperPolynomial
    (curve : RationalCurve) (box : Box) (parameter : Coordinate)
    (denominatorNonzero : curve.denominatorAt parameter ≠ 0) :
    (xUpperPolynomial curve box).eval parameter =
      normSq (curve.denominatorAt parameter) *
        (box.xUpper - (curve.point parameter).re) := by
  simp only [xUpperPolynomial, eval_sub, eval_scale,
    eval_affineRealNumerator_eq_point_mul_normSq curve parameter
      denominatorNonzero,
    eval_denominatorNormSq]
  ring1

@[simp] theorem eval_yLowerPolynomial
    (curve : RationalCurve) (box : Box) (parameter : Coordinate)
    (denominatorNonzero : curve.denominatorAt parameter ≠ 0) :
    (yLowerPolynomial curve box).eval parameter =
      normSq (curve.denominatorAt parameter) *
        ((curve.point parameter).im - box.yLower) := by
  simp only [yLowerPolynomial, eval_sub, eval_scale,
    eval_affineImaginaryNumerator_eq_point_mul_normSq curve parameter
      denominatorNonzero,
    eval_denominatorNormSq]
  ring1

@[simp] theorem eval_yUpperPolynomial
    (curve : RationalCurve) (box : Box) (parameter : Coordinate)
    (denominatorNonzero : curve.denominatorAt parameter ≠ 0) :
    (yUpperPolynomial curve box).eval parameter =
      normSq (curve.denominatorAt parameter) *
        (box.yUpper - (curve.point parameter).im) := by
  simp only [yUpperPolynomial, eval_sub, eval_scale,
    eval_affineImaginaryNumerator_eq_point_mul_normSq curve parameter
      denominatorNonzero,
    eval_denominatorNormSq]
  ring1

/-- If all four cleared box conditions are greater than the same negative
denominator-scaled radius, the displayed affine point lies within that
rational coordinate radius of the box.  This is a direct finite estimate;
it does not complete the point or assert a curve root. -/
theorem point_within_radius_of_condition_lower
    (curve : RationalCurve) (box : Box) (parameter radius lower : Coordinate)
    (radiusNonnegative : 0 ≤ radius)
    (denominatorNonzero : curve.denominatorAt parameter ≠ 0)
    (lowerLeDenominator : lower ≤
      normSq (curve.denominatorAt parameter))
    (xLower : -(lower * radius) <
      (xLowerPolynomial curve box).eval parameter)
    (xUpper : -(lower * radius) <
      (xUpperPolynomial curve box).eval parameter)
    (yLower : -(lower * radius) <
      (yLowerPolynomial curve box).eval parameter)
    (yUpper : -(lower * radius) <
      (yUpperPolynomial curve box).eval parameter) :
    box.xLower - radius < (curve.point parameter).re ∧
      (curve.point parameter).re < box.xUpper + radius ∧
      box.yLower - radius < (curve.point parameter).im ∧
      (curve.point parameter).im < box.yUpper + radius := by
  let denominatorNorm := normSq (curve.denominatorAt parameter)
  have denominatorPositive : 0 < denominatorNorm := by
    simpa only [denominatorNorm] using normSq_pos denominatorNonzero
  have scaledLower : lower * radius ≤ denominatorNorm * radius :=
    RFAP.ConstructiveFraction.mul_le_mul_of_nonneg_right_direct
      lowerLeDenominator radiusNonnegative
  have cancelLower {delta condition : Coordinate}
      (conditionEq : condition = denominatorNorm * delta)
      (conditionLower : -(lower * radius) < condition) :
      -radius < delta := by
    apply RFAP.ConstructiveFraction.lt_of_mul_lt_mul_right_direct
      (c := denominatorNorm) _ denominatorPositive
    calc
      -radius * denominatorNorm = -(denominatorNorm * radius) := by ring1
      _ ≤ -(lower * radius) :=
        RFAP.ConstructiveFraction.neg_le_neg_direct scaledLower
      _ < condition := conditionLower
      _ = delta * denominatorNorm := by rw [conditionEq]; ring1
  have leftDelta : -radius < (curve.point parameter).re - box.xLower :=
    cancelLower
      (eval_xLowerPolynomial curve box parameter denominatorNonzero) xLower
  have rightDelta : -radius < box.xUpper - (curve.point parameter).re :=
    cancelLower
      (eval_xUpperPolynomial curve box parameter denominatorNonzero) xUpper
  have bottomDelta : -radius < (curve.point parameter).im - box.yLower :=
    cancelLower
      (eval_yLowerPolynomial curve box parameter denominatorNonzero) yLower
  have topDelta : -radius < box.yUpper - (curve.point parameter).im :=
    cancelLower
      (eval_yUpperPolynomial curve box parameter denominatorNonzero) yUpper
  refine ⟨?_, ?_, ?_, ?_⟩
  · calc
      box.xLower - radius = -radius + box.xLower := by ring1
      _ < ((curve.point parameter).re - box.xLower) + box.xLower :=
        RFAP.ConstructiveFraction.add_lt_add_right_direct leftDelta box.xLower
      _ = (curve.point parameter).re := by ring1
  · have shifted := RFAP.ConstructiveFraction.add_lt_add_right_direct
      rightDelta (curve.point parameter).re
    calc
      (curve.point parameter).re =
          (-radius + (curve.point parameter).re) + radius := by ring1
      _ < (box.xUpper - (curve.point parameter).re +
          (curve.point parameter).re) + radius :=
        RFAP.ConstructiveFraction.add_lt_add_right_direct shifted radius
      _ = box.xUpper + radius := by ring1
  · calc
      box.yLower - radius = -radius + box.yLower := by ring1
      _ < ((curve.point parameter).im - box.yLower) + box.yLower :=
        RFAP.ConstructiveFraction.add_lt_add_right_direct bottomDelta box.yLower
      _ = (curve.point parameter).im := by ring1
  · have shifted := RFAP.ConstructiveFraction.add_lt_add_right_direct
      topDelta (curve.point parameter).im
    calc
      (curve.point parameter).im =
          (-radius + (curve.point parameter).im) + radius := by ring1
      _ < (box.yUpper - (curve.point parameter).im +
          (curve.point parameter).im) + radius :=
        RFAP.ConstructiveFraction.add_lt_add_right_direct shifted radius
      _ = box.yUpper + radius := by ring1

/-- The cleared weak signs are exactly closed-box membership at every
non-pole parameter. -/
theorem holds_iff_contains
    (curve : RationalCurve) (box : Box) (parameter : Coordinate)
    (denominatorNonzero : curve.denominatorAt parameter ≠ 0) :
    Holds curve box parameter ↔ box.Contains (curve.point parameter) := by
  let denominatorNorm := normSq (curve.denominatorAt parameter)
  have denominatorPositive : 0 < denominatorNorm :=
    normSq_pos denominatorNonzero
  simp only [Holds, RFAP.Boxes.Box.Contains,
    eval_xLowerPolynomial curve box parameter denominatorNonzero,
    eval_xUpperPolynomial curve box parameter denominatorNonzero,
    eval_yLowerPolynomial curve box parameter denominatorNonzero,
    eval_yUpperPolynomial curve box parameter denominatorNonzero]
  constructor
  · rintro ⟨left, right, bottom, top⟩
    exact ⟨
      sub_nonneg.mp (nonneg_of_mul_nonneg_right left denominatorPositive),
      sub_nonneg.mp (nonneg_of_mul_nonneg_right right denominatorPositive),
      sub_nonneg.mp (nonneg_of_mul_nonneg_right bottom denominatorPositive),
      sub_nonneg.mp (nonneg_of_mul_nonneg_right top denominatorPositive)⟩
  · rintro ⟨left, right, bottom, top⟩
    exact ⟨
      RFAP.ConstructiveFraction.mul_nonneg_direct denominatorPositive.le
        (sub_nonneg.mpr left),
      RFAP.ConstructiveFraction.mul_nonneg_direct denominatorPositive.le
        (sub_nonneg.mpr right),
      RFAP.ConstructiveFraction.mul_nonneg_direct denominatorPositive.le
        (sub_nonneg.mpr bottom),
      RFAP.ConstructiveFraction.mul_nonneg_direct denominatorPositive.le
        (sub_nonneg.mpr top)⟩

/-- The cleared strict signs are exactly strict box-interior membership. -/
theorem strictHolds_iff_strictContains
    (curve : RationalCurve) (box : Box) (parameter : Coordinate)
    (denominatorNonzero : curve.denominatorAt parameter ≠ 0) :
    StrictHolds curve box parameter ↔
      box.StrictContains (curve.point parameter) := by
  let denominatorNorm := normSq (curve.denominatorAt parameter)
  have denominatorPositive : 0 < denominatorNorm :=
    normSq_pos denominatorNonzero
  simp only [StrictHolds, RFAP.Boxes.Box.StrictContains,
    eval_xLowerPolynomial curve box parameter denominatorNonzero,
    eval_xUpperPolynomial curve box parameter denominatorNonzero,
    eval_yLowerPolynomial curve box parameter denominatorNonzero,
    eval_yUpperPolynomial curve box parameter denominatorNonzero]
  constructor
  · rintro ⟨left, right, bottom, top⟩
    exact ⟨
      RFAP.ConstructiveFraction.lt_of_sub_pos_direct
        (RFAP.ConstructiveFraction.pos_of_mul_pos_right_direct
          left denominatorPositive.le),
      RFAP.ConstructiveFraction.lt_of_sub_pos_direct
        (RFAP.ConstructiveFraction.pos_of_mul_pos_right_direct
          right denominatorPositive.le),
      RFAP.ConstructiveFraction.lt_of_sub_pos_direct
        (RFAP.ConstructiveFraction.pos_of_mul_pos_right_direct
          bottom denominatorPositive.le),
      RFAP.ConstructiveFraction.lt_of_sub_pos_direct
        (RFAP.ConstructiveFraction.pos_of_mul_pos_right_direct
          top denominatorPositive.le)⟩
  · rintro ⟨left, right, bottom, top⟩
    exact ⟨
      RFAP.ConstructiveFraction.mul_pos_direct denominatorPositive
        (RFAP.ConstructiveFraction.sub_pos_direct left),
      RFAP.ConstructiveFraction.mul_pos_direct denominatorPositive
        (RFAP.ConstructiveFraction.sub_pos_direct right),
      RFAP.ConstructiveFraction.mul_pos_direct denominatorPositive
        (RFAP.ConstructiveFraction.sub_pos_direct bottom),
      RFAP.ConstructiveFraction.mul_pos_direct denominatorPositive
        (RFAP.ConstructiveFraction.sub_pos_direct top)⟩

/-- Drop only identically-zero box-edge conditions before forming a common
cut guard. -/
def activeConditionPolynomials (curve : RationalCurve) (box : Box) :
    List CoordinatePolynomial :=
  (conditionPolynomials curve box).filter fun polynomial =>
    polynomial.isZero = false

theorem activeConditionPolynomials_all_nonzero
    (curve : RationalCurve) (box : Box) :
    (activeConditionPolynomials curve box).Forall fun polynomial =>
      polynomial.isZero = false := by
  rw [List.forall_iff_forall_mem]
  intro polynomial member
  exact of_decide_eq_true (List.mem_filter.mp member).2

/-- One represented nonzero polynomial clearing every nontrivial box-edge
condition at a common rational cut. -/
def conditionGuard (curve : RationalCurve) (box : Box) :
    CoordinatePolynomial :=
  RFAP.SturmRootCount.polynomialProduct
    (activeConditionPolynomials curve box)

theorem conditionGuard_isZero_false (curve : RationalCurve) (box : Box) :
    (conditionGuard curve box).isZero = false := by
  exact RFAP.SturmRootCount.polynomialProduct_isZero_false
    (activeConditionPolynomials_all_nonzero curve box)

theorem eval_ne_zero_of_active_condition
    {curve : RationalCurve} {box : Box} {polynomial : CoordinatePolynomial}
    {parameter : Coordinate}
    (member : polynomial ∈ activeConditionPolynomials curve box)
    (guardNonzero : (conditionGuard curve box).eval parameter ≠ 0) :
    polynomial.eval parameter ≠ 0 := by
  exact RFAP.SturmRootCount.eval_ne_zero_of_mem_of_polynomialProduct
    member guardNonzero

/-- Every one of the four box conditions is either an identically-zero edge
condition or a member of the common nonzero guard family. -/
theorem condition_zero_or_active
    {curve : RationalCurve} {box : Box} {polynomial : CoordinatePolynomial}
    (member : polynomial ∈ conditionPolynomials curve box) :
    polynomial.isZero = true ∨
      polynomial ∈ activeConditionPolynomials curve box := by
  cases zero : polynomial.isZero with
  | true => exact Or.inl rfl
  | false =>
      exact Or.inr (List.mem_filter.mpr ⟨member, decide_eq_true zero⟩)

end CCL.CurveBoxConditions
