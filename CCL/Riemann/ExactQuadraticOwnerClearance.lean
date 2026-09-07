import CCL.Riemann.SquareRootContinuationChain

/-!
# Exact boundary clearance for a displayed quadratic owner

For an owner of `Z² - parameter`, the four side-resultant determinants are
explicit rational expressions.  When all four are nonzero, this module
repackages the existing winding-one box with the exact resultant clearances.
If any check fails, it returns the original owner.  The operation is therefore
total, constructive, executable, and never weakens the inherited clearance.
-/

namespace CCL.Riemann.ExactQuadraticOwnerClearance

abbrev Coordinate := RFAP.ConstructiveFraction.Rational
abbrev Gaussian := RFAP.ConstructiveGaussian.Gaussian
abbrev GaussianPolynomial :=
  RFAP.ConstructivePolynomial.GaussianPolynomial
abbrev Polynomial := RFAP.ComputablePolynomial.DensePolynomial Coordinate
abbrev Box := RFAP.Boxes.Box
abbrev Owner := CCL.Riemann.SquareRootContinuationChain.Owner

/-- The boundary-clearance bound of an owner is no larger than any of its
four ambient-line bounds.  This finite invariant lets one displacement check
justify all five constant-term transports. -/
structure AmbientClearanceDominance {parameter : Gaussian}
    (owner : Owner parameter) : Prop where
  left : owner.track.initial.clearance.bound <=
    owner.track.initial.ambientLeftClearance.bound
  right : owner.track.initial.clearance.bound <=
    owner.track.initial.ambientRightClearance.bound
  bottom : owner.track.initial.clearance.bound <=
    owner.track.initial.ambientBottomClearance.bound
  top : owner.track.initial.clearance.bound <=
    owner.track.initial.ambientTopClearance.bound

namespace AmbientClearanceDominance

/-- A move smaller than the boundary clearance is automatically smaller than
all four ambient-line clearances when the owner carries the dominance
invariant. -/
theorem ambientSmallness {source target : Gaussian} {owner : Owner source}
    (dominance : AmbientClearanceDominance owner)
    (small : RFAP.ConstructiveGaussian.Gaussian.normSq (source - target) <
      owner.track.initial.clearance.bound) :
    RFAP.ConstructiveGaussian.Gaussian.normSq (source - target) <
        owner.track.initial.ambientLeftClearance.bound /\
      RFAP.ConstructiveGaussian.Gaussian.normSq (source - target) <
          owner.track.initial.ambientRightClearance.bound /\
        RFAP.ConstructiveGaussian.Gaussian.normSq (source - target) <
            owner.track.initial.ambientBottomClearance.bound /\
          RFAP.ConstructiveGaussian.Gaussian.normSq (source - target) <
            owner.track.initial.ambientTopClearance.bound :=
  ⟨small.trans_le dominance.left, small.trans_le dominance.right,
    small.trans_le dominance.bottom, small.trans_le dominance.top⟩

end AmbientClearanceDominance

private def rootPolynomial (parameter : Gaussian) : GaussianPolynomial :=
  CCL.PowerMonodromy.polynomial parameter
    CCL.Riemann.SquareRootSheets.degreeTwo

section QuadraticPathCoefficients

open RFAP.ComputablePolynomial.DensePolynomial

private theorem quadratic_add_constant
    {leading : Gaussian} (middle trailing constantTerm : Gaussian)
    (leadingNonzero : leading ≠ 0) :
    (⟨[leading, middle, trailing]⟩ : GaussianPolynomial) +
        constant constantTerm =
      ⟨[leading, middle, trailing + constantTerm]⟩ := by
  apply RFAP.ComputablePolynomial.DensePolynomial.ext
  change (RFAP.ComputablePolynomial.DensePolynomial.add
      ⟨[leading, middle, trailing]⟩ (constant constantTerm)).coeffs = _
  simp [RFAP.ComputablePolynomial.DensePolynomial.add, padLeft, normalize,
    constant, leadingNonzero]

private theorem mulLine_two_coeffs
    (origin direction a b : Gaussian)
    (originNonzero : origin ≠ 0) (directionNonzero : direction ≠ 0)
    (leadingNonzero : a ≠ 0) (polynomial : GaussianPolynomial)
    (coefficients : polynomial.coeffs = [a, b]) :
    (RFAP.PathPolynomial.mulLine origin direction polynomial).coeffs =
      [direction * a, direction * b + origin * a, origin * b] := by
  unfold RFAP.PathPolynomial.mulLine
  have normalized : polynomial.normalize.coeffs = [a, b] := by
    rw [normalize_coeffs, coefficients]
    simp [leadingNonzero]
  let originScaled : GaussianPolynomial :=
    ⟨[origin * a, origin * b]⟩
  let directionScaled : GaussianPolynomial :=
    ⟨[direction * a, direction * b]⟩
  have originScaleEq : scale origin polynomial = originScaled := by
    apply RFAP.ComputablePolynomial.DensePolynomial.ext
    rw [scale_coeffs_of_ne_zero originNonzero, normalized]
    rfl
  have directionScaleEq : scale direction polynomial = directionScaled := by
    apply RFAP.ComputablePolynomial.DensePolynomial.ext
    rw [scale_coeffs_of_ne_zero directionNonzero, normalized]
    rfl
  rw [originScaleEq, directionScaleEq]
  have directionScaledNormalized :
      directionScaled.normalize = directionScaled := by
    apply RFAP.ComputablePolynomial.DensePolynomial.ext
    unfold directionScaled normalize
    simp [directionNonzero, leadingNonzero,
      RFAP.ComputablePolynomial.DensePolynomial.mul_ne_zero_direct]
  unfold shift
  rw [if_neg]
  · rw [congrArg RFAP.ComputablePolynomial.DensePolynomial.coeffs
      directionScaledNormalized]
    change (RFAP.ComputablePolynomial.DensePolynomial.add originScaled
      ⟨[direction * a, direction * b, 0]⟩).coeffs = _
    unfold RFAP.ComputablePolynomial.DensePolynomial.add originScaled normalize
    simp [padLeft, directionNonzero, leadingNonzero,
      RFAP.ComputablePolynomial.DensePolynomial.mul_ne_zero_direct]
    exact add_comm _ _
  · unfold isZero directionScaled normalize
    simp [directionNonzero, leadingNonzero,
      RFAP.ComputablePolynomial.DensePolynomial.mul_ne_zero_direct]

private theorem composeLine_quadratic
    (parameter origin direction : Gaussian)
    (originNonzero : origin ≠ 0) (directionNonzero : direction ≠ 0) :
    RFAP.PathPolynomial.composeLine
        (CCL.PowerMonodromy.polynomial parameter
          CCL.Riemann.SquareRootSheets.degreeTwo)
        origin direction =
      ⟨[direction * direction,
        direction * origin + origin * direction,
        origin * origin - parameter]⟩ := by
  unfold RFAP.PathPolynomial.composeLine
    RFAP.PathPolynomial.composeLineCoeffs
    CCL.PowerMonodromy.polynomial CCL.RootPowers.rootPolynomial
    CCL.Riemann.SquareRootSheets.degreeTwo
  simp only [List.replicate_succ, List.replicate_zero, List.nil_append,
    List.cons_append, List.foldl_cons, List.foldl_nil]
  rw [RFAP.PathPolynomial.mulLine_zero, zero_add_normalize,
    normalize_constant_of_ne one_ne_zero]
  have first : RFAP.PathPolynomial.mulLine origin direction (constant 1) =
      (⟨[direction, origin]⟩ : GaussianPolynomial) := by
    rw [RFAP.PathPolynomial.mulLine, scale_constant, scale_constant,
      RFAP.ConstructiveGaussian.Gaussian.mul_one,
      RFAP.ConstructiveGaussian.Gaussian.mul_one,
      normalize_constant_of_ne directionNonzero,
      shift_one_constant_of_ne directionNonzero,
      normalize_constant_of_ne originNonzero,
      constant_add_linear origin directionNonzero]
  have linearNormalized :
      (⟨[direction, origin]⟩ : GaussianPolynomial).normalize =
        ⟨[direction, origin]⟩ := by
    apply RFAP.ComputablePolynomial.DensePolynomial.ext
    simp [normalize, directionNonzero]
  rw [first, add_constant_zero, linearNormalized]
  have secondMul :
      RFAP.PathPolynomial.mulLine origin direction
          (⟨[direction, origin]⟩ : GaussianPolynomial) =
        ⟨[direction * direction, direction * origin + origin * direction,
          origin * origin]⟩ := by
    apply RFAP.ComputablePolynomial.DensePolynomial.ext
    exact mulLine_two_coeffs origin direction direction origin
      originNonzero directionNonzero directionNonzero
        ⟨[direction, origin]⟩ rfl
  rw [secondMul, quadratic_add_constant
    (direction * origin + origin * direction) (origin * origin)
      (-parameter)
      (RFAP.ConstructiveGaussian.Gaussian.mul_ne_zero_direct
        directionNonzero directionNonzero)]
  simp only [RFAP.ConstructiveGaussian.Gaussian.sub_eq_add_neg]

/-- Exact three real coefficients of `Z²-parameter` on a nonzero vertical
line.  This is the compact Horner cache used by explicit transport bounds. -/
theorem quadraticVerticalPathReal (parameter : Gaussian) (x : Coordinate)
    (xNonzero : x ≠ 0) :
    RFAP.PathPolynomial.pathReal
        (CCL.PowerMonodromy.polynomial parameter
          CCL.Riemann.SquareRootSheets.degreeTwo)
        (RFAP.Winding.verticalBase x) RFAP.Winding.verticalDirection =
      (⟨[-1, 0, x ^ 2 - parameter.re]⟩ : Polynomial) := by
  unfold RFAP.PathPolynomial.pathReal
  rw [composeLine_quadratic]
  · apply RFAP.ComputablePolynomial.DensePolynomial.ext
    simp only [RFAP.PathPolynomial.realPart, List.map_cons, List.map_nil,
      RFAP.ConstructiveGaussian.Gaussian.mul_re,
      RFAP.ConstructiveGaussian.Gaussian.add_re,
      RFAP.ConstructiveGaussian.Gaussian.sub_re,
      RFAP.Winding.verticalBase, RFAP.Winding.verticalDirection]
    congr 3 <;> ring1
  · intro zero
    have real := congrArg (fun value : Gaussian => value.re) zero
    exact xNonzero real
  · intro zero
    have imaginary := congrArg (fun value : Gaussian => value.im) zero
    exact (by decide : (1 : Coordinate) ≠ 0) imaginary

/-- Exact three imaginary coefficients of `Z²-parameter` on a nonzero
vertical line. -/
theorem quadraticVerticalPathImag (parameter : Gaussian) (x : Coordinate)
    (xNonzero : x ≠ 0) :
    RFAP.PathPolynomial.pathImag
        (CCL.PowerMonodromy.polynomial parameter
          CCL.Riemann.SquareRootSheets.degreeTwo)
        (RFAP.Winding.verticalBase x) RFAP.Winding.verticalDirection =
      (⟨[0, 2 * x, -parameter.im]⟩ : Polynomial) := by
  unfold RFAP.PathPolynomial.pathImag
  rw [composeLine_quadratic]
  · apply RFAP.ComputablePolynomial.DensePolynomial.ext
    simp only [RFAP.PathPolynomial.imagPart, List.map_cons, List.map_nil,
      RFAP.ConstructiveGaussian.Gaussian.mul_im,
      RFAP.ConstructiveGaussian.Gaussian.add_im,
      RFAP.ConstructiveGaussian.Gaussian.sub_im,
      RFAP.Winding.verticalBase, RFAP.Winding.verticalDirection]
    congr 3 <;> ring1
  · intro zero
    have real := congrArg (fun value : Gaussian => value.re) zero
    exact xNonzero real
  · intro zero
    have imaginary := congrArg (fun value : Gaussian => value.im) zero
    exact (by decide : (1 : Coordinate) ≠ 0) imaginary

/-- Exact three real coefficients of `Z²-parameter` on a nonzero horizontal
line. -/
theorem quadraticHorizontalPathReal (parameter : Gaussian) (y : Coordinate)
    (yNonzero : y ≠ 0) :
    RFAP.PathPolynomial.pathReal
        (CCL.PowerMonodromy.polynomial parameter
          CCL.Riemann.SquareRootSheets.degreeTwo)
        (RFAP.Winding.horizontalBase y) RFAP.Winding.horizontalDirection =
      (⟨[1, 0, -(y ^ 2) - parameter.re]⟩ : Polynomial) := by
  unfold RFAP.PathPolynomial.pathReal
  rw [composeLine_quadratic]
  · apply RFAP.ComputablePolynomial.DensePolynomial.ext
    simp only [RFAP.PathPolynomial.realPart, List.map_cons, List.map_nil,
      RFAP.ConstructiveGaussian.Gaussian.mul_re,
      RFAP.ConstructiveGaussian.Gaussian.add_re,
      RFAP.ConstructiveGaussian.Gaussian.sub_re,
      RFAP.Winding.horizontalBase, RFAP.Winding.horizontalDirection]
    congr 3 <;> ring1
  · intro zero
    have imaginary := congrArg (fun value : Gaussian => value.im) zero
    exact yNonzero imaginary
  · intro zero
    have real := congrArg (fun value : Gaussian => value.re) zero
    exact (by decide : (1 : Coordinate) ≠ 0) real

/-- Exact three imaginary coefficients of `Z²-parameter` on a nonzero
horizontal line. -/
theorem quadraticHorizontalPathImag (parameter : Gaussian) (y : Coordinate)
    (yNonzero : y ≠ 0) :
    RFAP.PathPolynomial.pathImag
        (CCL.PowerMonodromy.polynomial parameter
          CCL.Riemann.SquareRootSheets.degreeTwo)
        (RFAP.Winding.horizontalBase y) RFAP.Winding.horizontalDirection =
      (⟨[0, 2 * y, -parameter.im]⟩ : Polynomial) := by
  unfold RFAP.PathPolynomial.pathImag
  rw [composeLine_quadratic]
  · apply RFAP.ComputablePolynomial.DensePolynomial.ext
    simp only [RFAP.PathPolynomial.imagPart, List.map_cons, List.map_nil,
      RFAP.ConstructiveGaussian.Gaussian.mul_im,
      RFAP.ConstructiveGaussian.Gaussian.add_im,
      RFAP.ConstructiveGaussian.Gaussian.sub_im,
      RFAP.Winding.horizontalBase, RFAP.Winding.horizontalDirection]
    congr 3 <;> ring1
  · intro zero
    have imaginary := congrArg (fun value : Gaussian => value.im) zero
    exact yNonzero imaginary
  · intro zero
    have real := congrArg (fun value : Gaussian => value.re) zero
    exact (by decide : (1 : Coordinate) ≠ 0) real

end QuadraticPathCoefficients

/-- A positive squared rational remains positive without invoking a completed
ordered field. -/
private theorem sq_pos_of_ne_zero {value : Coordinate}
    (nonzero : value ≠ 0) : 0 < value ^ 2 := by
  have squareNonzero : value ^ 2 ≠ 0 := by
    intro zero
    exact nonzero ((RFAP.ConstructiveFraction.sq_eq_zero_direct value).mp zero)
  exact lt_of_le_of_ne (RFAP.ConstructiveFraction.sq_nonneg_direct value)
    (Ne.symm squareNonzero)

private theorem add_sq_le_two (left right : Coordinate) :
    (left + right) ^ 2 ≤ 2 * (left ^ 2 + right ^ 2) := by
  apply sub_nonneg.mp
  calc
    0 ≤ (left - right) ^ 2 :=
      RFAP.ConstructiveFraction.sq_nonneg_direct _
    _ = 2 * (left ^ 2 + right ^ 2) - (left + right) ^ 2 := by
      ring1

private theorem threeCoefficientHorner_le
    (polynomial : Polynomial) (a b c : Coordinate)
    (coefficients : polynomial.coeffs = [a, b, c])
    (interval : RFAP.PathClearance.Interval)
    (radiusLe : interval.squareBound ≤ 16)
    (aSqLe : a ^ 2 ≤ 1) (bSqLe : b ^ 2 ≤ 64)
    (cSqLe : c ^ 2 ≤ 1024) :
    RFAP.PathClearance.evalSqBound polynomial interval ≤ 32768 := by
  calc
    RFAP.PathClearance.evalSqBound polynomial interval ≤
        2 * ((2 * ((2 * (1 : Coordinate)) * 16 + 64)) * 16 + 1024) :=
      RFAP.PathClearance.evalSqBound_three_le polynomial a b c coefficients
        interval 16 1 64 1024
        (RFAP.ConstructiveFraction.natCast_pos_direct
          (n := 16) (by decide)).le
        (RFAP.ConstructiveFraction.natCast_pos_direct
          (n := 1) (by decide)).le
        (RFAP.ConstructiveFraction.natCast_pos_direct
          (n := 64) (by decide)).le
        radiusLe aSqLe bSqLe cSqLe
    _ = 8192 := by ring1
    _ ≤ 32768 := by
      change ((8192 : Nat) : Coordinate) ≤ ((32768 : Nat) : Coordinate)
      exact RFAP.ConstructiveFraction.natCast_le_direct (by decide)

private theorem coordinateSquare_add_component_sq_le
    (coordinate component : Coordinate)
    (coordinateSqLe : coordinate ^ 2 ≤ 16)
    (componentSqLe : component ^ 2 ≤ 256) :
    (coordinate ^ 2 + component) ^ 2 ≤ 1024 := by
  have coordinateFourthLe : (coordinate ^ 2) ^ 2 ≤ (16 : Coordinate) ^ 2 :=
    RFAP.ConstructiveFraction.pow_le_pow_direct
      (RFAP.ConstructiveFraction.sq_nonneg_direct coordinate)
      coordinateSqLe 2
  calc
    (coordinate ^ 2 + component) ^ 2 ≤
        2 * ((coordinate ^ 2) ^ 2 + component ^ 2) :=
      add_sq_le_two _ _
    _ ≤ 2 * ((16 : Coordinate) ^ 2 + 256) :=
      RFAP.ConstructiveFraction.mul_le_mul_of_nonneg_left_direct
        (add_le_add coordinateFourthLe componentSqLe) (by decide)
    _ = 1024 := by ring1

private theorem doubledCoordinate_sq_le
    (coordinate : Coordinate) (coordinateSqLe : coordinate ^ 2 ≤ 16) :
    (2 * coordinate) ^ 2 ≤ 64 := by
  calc
    (2 * coordinate) ^ 2 = 4 * coordinate ^ 2 := by ring1
    _ ≤ 4 * 16 :=
      RFAP.ConstructiveFraction.mul_le_mul_of_nonneg_left_direct
        coordinateSqLe (by decide)
    _ = 64 := by ring1

/-- On a quadratic vertical line contained in the displayed radius-`4`
interval, a radius-`16` parameter norm bounds the complete finite Horner
majorant by `65536`. -/
theorem quadraticVerticalBoundarySideMajorant_le
    (parameter : Gaussian) (x : Coordinate) (xNonzero : x ≠ 0)
    (interval : RFAP.PathClearance.Interval)
    (intervalSqLe : interval.squareBound ≤ 16)
    (xSqLe : x ^ 2 ≤ 16)
    (parameterNormSqLe :
      RFAP.ConstructiveGaussian.Gaussian.normSq parameter ≤ 256) :
    RFAP.WindingHomotopy.boundarySideMajorant
        (CCL.PowerMonodromy.polynomial parameter
          CCL.Riemann.SquareRootSheets.degreeTwo)
        (RFAP.Winding.verticalBase x) RFAP.Winding.verticalDirection
        interval ≤ 65536 := by
  have parameterRealSqLe : parameter.re ^ 2 ≤ 256 :=
    (le_add_of_nonneg_right
      (RFAP.ConstructiveFraction.sq_nonneg_direct parameter.im)).trans
        parameterNormSqLe
  have parameterImagSqLe : parameter.im ^ 2 ≤ 256 :=
    (le_add_of_nonneg_left
      (RFAP.ConstructiveFraction.sq_nonneg_direct parameter.re)).trans
        parameterNormSqLe
  have realConstantSqLe : (x ^ 2 - parameter.re) ^ 2 ≤ 1024 := by
    rw [show x ^ 2 - parameter.re = x ^ 2 + (-parameter.re) by ring1]
    apply coordinateSquare_add_component_sq_le x (-parameter.re) xSqLe
    simpa only [neg_sq] using parameterRealSqLe
  have imagConstantSqLe : (-parameter.im) ^ 2 ≤ 1024 := by
    calc
      (-parameter.im) ^ 2 = parameter.im ^ 2 := by ring1
      _ ≤ 256 := parameterImagSqLe
      _ ≤ 1024 := by
        change ((256 : Nat) : Coordinate) ≤ ((1024 : Nat) : Coordinate)
        exact RFAP.ConstructiveFraction.natCast_le_direct (by decide)
  have realLe : RFAP.PathClearance.evalSqBound
      (RFAP.PathPolynomial.pathReal
        (CCL.PowerMonodromy.polynomial parameter
          CCL.Riemann.SquareRootSheets.degreeTwo)
        (RFAP.Winding.verticalBase x) RFAP.Winding.verticalDirection)
      interval ≤ 32768 := by
    rw [quadraticVerticalPathReal parameter x xNonzero]
    apply threeCoefficientHorner_le _ (-1) 0 (x ^ 2 - parameter.re) rfl
      interval intervalSqLe
    · rw [show (-1 : Coordinate) ^ 2 = 1 by ring1]
    · exact (RFAP.ConstructiveFraction.sq_nonneg_direct 0).trans
        (RFAP.ConstructiveFraction.natCast_pos_direct
          (n := 64) (by decide)).le
    · exact realConstantSqLe
  have imaginaryLe : RFAP.PathClearance.evalSqBound
      (RFAP.PathPolynomial.pathImag
        (CCL.PowerMonodromy.polynomial parameter
          CCL.Riemann.SquareRootSheets.degreeTwo)
        (RFAP.Winding.verticalBase x) RFAP.Winding.verticalDirection)
      interval ≤ 32768 := by
    rw [quadraticVerticalPathImag parameter x xNonzero]
    apply threeCoefficientHorner_le _ 0 (2 * x) (-parameter.im) rfl
      interval intervalSqLe
    · exact (RFAP.ConstructiveFraction.sq_nonneg_direct 0).trans
        (RFAP.ConstructiveFraction.natCast_pos_direct
          (n := 1) (by decide)).le
    · exact doubledCoordinate_sq_le x xSqLe
    · exact imagConstantSqLe
  unfold RFAP.WindingHomotopy.boundarySideMajorant
  apply max_le
  · change ((1 : Nat) : Coordinate) ≤ ((65536 : Nat) : Coordinate)
    exact RFAP.ConstructiveFraction.natCast_le_direct (by decide)
  · calc
      RFAP.PathClearance.evalSqBound
            (RFAP.PathPolynomial.pathReal
              (CCL.PowerMonodromy.polynomial parameter
                CCL.Riemann.SquareRootSheets.degreeTwo)
              (RFAP.Winding.verticalBase x) RFAP.Winding.verticalDirection)
            interval +
          RFAP.PathClearance.evalSqBound
            (RFAP.PathPolynomial.pathImag
              (CCL.PowerMonodromy.polynomial parameter
                CCL.Riemann.SquareRootSheets.degreeTwo)
              (RFAP.Winding.verticalBase x) RFAP.Winding.verticalDirection)
            interval ≤ 32768 + 32768 := add_le_add realLe imaginaryLe
      _ = 65536 := by ring1

/-- Horizontal counterpart of `quadraticVerticalBoundarySideMajorant_le`. -/
theorem quadraticHorizontalBoundarySideMajorant_le
    (parameter : Gaussian) (y : Coordinate) (yNonzero : y ≠ 0)
    (interval : RFAP.PathClearance.Interval)
    (intervalSqLe : interval.squareBound ≤ 16)
    (ySqLe : y ^ 2 ≤ 16)
    (parameterNormSqLe :
      RFAP.ConstructiveGaussian.Gaussian.normSq parameter ≤ 256) :
    RFAP.WindingHomotopy.boundarySideMajorant
        (CCL.PowerMonodromy.polynomial parameter
          CCL.Riemann.SquareRootSheets.degreeTwo)
        (RFAP.Winding.horizontalBase y) RFAP.Winding.horizontalDirection
        interval ≤ 65536 := by
  have parameterRealSqLe : parameter.re ^ 2 ≤ 256 :=
    (le_add_of_nonneg_right
      (RFAP.ConstructiveFraction.sq_nonneg_direct parameter.im)).trans
        parameterNormSqLe
  have parameterImagSqLe : parameter.im ^ 2 ≤ 256 :=
    (le_add_of_nonneg_left
      (RFAP.ConstructiveFraction.sq_nonneg_direct parameter.re)).trans
        parameterNormSqLe
  have realConstantSqLe : (-(y ^ 2) - parameter.re) ^ 2 ≤ 1024 := by
    rw [show (-(y ^ 2) - parameter.re) ^ 2 =
      (y ^ 2 + parameter.re) ^ 2 by ring1]
    exact coordinateSquare_add_component_sq_le y parameter.re ySqLe
      parameterRealSqLe
  have imagConstantSqLe : (-parameter.im) ^ 2 ≤ 1024 := by
    calc
      (-parameter.im) ^ 2 = parameter.im ^ 2 := by ring1
      _ ≤ 256 := parameterImagSqLe
      _ ≤ 1024 := by
        change ((256 : Nat) : Coordinate) ≤ ((1024 : Nat) : Coordinate)
        exact RFAP.ConstructiveFraction.natCast_le_direct (by decide)
  have realLe : RFAP.PathClearance.evalSqBound
      (RFAP.PathPolynomial.pathReal
        (CCL.PowerMonodromy.polynomial parameter
          CCL.Riemann.SquareRootSheets.degreeTwo)
        (RFAP.Winding.horizontalBase y) RFAP.Winding.horizontalDirection)
      interval ≤ 32768 := by
    rw [quadraticHorizontalPathReal parameter y yNonzero]
    apply threeCoefficientHorner_le _ 1 0 (-(y ^ 2) - parameter.re) rfl
      interval intervalSqLe
    · rw [show (1 : Coordinate) ^ 2 = 1 by ring1]
    · exact (RFAP.ConstructiveFraction.sq_nonneg_direct 0).trans
        (RFAP.ConstructiveFraction.natCast_pos_direct
          (n := 64) (by decide)).le
    · exact realConstantSqLe
  have imaginaryLe : RFAP.PathClearance.evalSqBound
      (RFAP.PathPolynomial.pathImag
        (CCL.PowerMonodromy.polynomial parameter
          CCL.Riemann.SquareRootSheets.degreeTwo)
        (RFAP.Winding.horizontalBase y) RFAP.Winding.horizontalDirection)
      interval ≤ 32768 := by
    rw [quadraticHorizontalPathImag parameter y yNonzero]
    apply threeCoefficientHorner_le _ 0 (2 * y) (-parameter.im) rfl
      interval intervalSqLe
    · exact (RFAP.ConstructiveFraction.sq_nonneg_direct 0).trans
        (RFAP.ConstructiveFraction.natCast_pos_direct
          (n := 1) (by decide)).le
    · exact doubledCoordinate_sq_le y ySqLe
    · exact imagConstantSqLe
  unfold RFAP.WindingHomotopy.boundarySideMajorant
  apply max_le
  · change ((1 : Nat) : Coordinate) ≤ ((65536 : Nat) : Coordinate)
    exact RFAP.ConstructiveFraction.natCast_le_direct (by decide)
  · calc
      RFAP.PathClearance.evalSqBound
            (RFAP.PathPolynomial.pathReal
              (CCL.PowerMonodromy.polynomial parameter
                CCL.Riemann.SquareRootSheets.degreeTwo)
              (RFAP.Winding.horizontalBase y)
                RFAP.Winding.horizontalDirection)
            interval +
          RFAP.PathClearance.evalSqBound
            (RFAP.PathPolynomial.pathImag
              (CCL.PowerMonodromy.polynomial parameter
                CCL.Riemann.SquareRootSheets.degreeTwo)
              (RFAP.Winding.horizontalBase y)
                RFAP.Winding.horizontalDirection)
            interval ≤ 32768 + 32768 := add_le_add realLe imaginaryLe
      _ = 65536 := by ring1

private theorem sum_product_sq_le_product_sums
    (a b first second : Coordinate) :
    (a * first + b * second) ^ 2 ≤
      (a ^ 2 + b ^ 2) * (first ^ 2 + second ^ 2) := by
  apply sub_nonneg.mp
  calc
    0 ≤ (a * second - b * first) ^ 2 :=
      RFAP.ConstructiveFraction.sq_nonneg_direct _
    _ = (a ^ 2 + b ^ 2) * (first ^ 2 + second ^ 2) -
          (a * first + b * second) ^ 2 := by
      ring1

/-- Finite coefficient majorant used by the direct quadratic side-clearance
formula.  Exposing the cached rational value lets explicit examples compare
side bounds after clearing one positive denominator, without unfolding the
full boundary-clearance certificate. -/
def directLineMajorant
    (constant slope intercept radiusSq : Coordinate) : Coordinate :=
  max 1 (constant ^ 2 + 2 * (slope ^ 2 * radiusSq + intercept ^ 2))

theorem directLineMajorant_positive
    (constant slope intercept radiusSq : Coordinate) :
    0 < directLineMajorant constant slope intercept radiusSq :=
  (show (0 : Coordinate) < 1 by decide).trans_le (le_max_left _ _)

/-- The rational resultant identity gives a direct norm-square lower bound.
Unlike the generic polynomial Bézout evaluator, this proof stores only one
resultant square, one short coefficient majorant, and one division. -/
private theorem directLineLower
    (coordinate radiusSq constant slope intercept determinant
      realPart imaginaryPart : Coordinate)
    (coordinateSq : coordinate ^ 2 ≤ radiusSq)
    (identity : determinant =
      constant * realPart + (slope * coordinate + intercept) * imaginaryPart) :
    determinant ^ 2 /
        directLineMajorant constant slope intercept radiusSq ≤
      realPart ^ 2 + imaginaryPart ^ 2 := by
  let linear := slope * coordinate + intercept
  let coefficientSq := constant ^ 2 + linear ^ 2
  let valueSq := realPart ^ 2 + imaginaryPart ^ 2
  have productLe : slope ^ 2 * coordinate ^ 2 ≤
      slope ^ 2 * radiusSq :=
    RFAP.ConstructiveFraction.mul_le_mul_of_nonneg_left_direct coordinateSq
      (RFAP.ConstructiveFraction.sq_nonneg_direct slope)
  have linearSqLe : linear ^ 2 ≤
      2 * (slope ^ 2 * radiusSq + intercept ^ 2) := by
    calc
      linear ^ 2 ≤
          2 * ((slope * coordinate) ^ 2 + intercept ^ 2) := by
        exact add_sq_le_two _ _
      _ = 2 * (slope ^ 2 * coordinate ^ 2 + intercept ^ 2) := by
        ring1
      _ ≤ 2 * (slope ^ 2 * radiusSq + intercept ^ 2) :=
        RFAP.ConstructiveFraction.mul_le_mul_of_nonneg_left_direct
          (add_le_add productLe le_rfl) (by decide)
  have coefficientLe : coefficientSq ≤
      directLineMajorant constant slope intercept radiusSq :=
    (add_le_add le_rfl linearSqLe).trans (le_max_right _ _)
  have valueNonnegative : 0 ≤ valueSq :=
    add_nonneg (RFAP.ConstructiveFraction.sq_nonneg_direct _)
      (RFAP.ConstructiveFraction.sq_nonneg_direct _)
  have cauchy : determinant ^ 2 ≤ coefficientSq * valueSq := by
    calc
      determinant ^ 2 =
          (constant * realPart + linear * imaginaryPart) ^ 2 := by
        rw [identity]
      _ ≤ coefficientSq * valueSq :=
        sum_product_sq_le_product_sums _ _ _ _
  have scaled : determinant ^ 2 ≤
      directLineMajorant constant slope intercept radiusSq * valueSq :=
    cauchy.trans
      (RFAP.ConstructiveFraction.mul_le_mul_of_nonneg_right_direct
        coefficientLe valueNonnegative)
  apply (RFAP.ConstructiveFraction.div_le_iff_pos
    (directLineMajorant_positive constant slope intercept radiusSq)).mpr
  rw [RFAP.ConstructiveFraction.mul_comm]
  exact scaled

/-- The executable lower bound used on one vertical side of a quadratic
owner box.  Naming the value independently of its proof certificate lets
explicit finite examples cache and compare the rational calculation without
reconstructing the side-clearance proof. -/
def directVerticalClearanceBound (parameter : Gaussian) (box : Box)
    (x : Coordinate) : Coordinate :=
  CCL.Riemann.SquareRootContinuationChain.Owner.verticalDeterminant
      parameter x ^ 2 /
    directLineMajorant (4 * x ^ 2) (2 * x) parameter.im
      (max (box.yLower ^ 2) (box.yUpper ^ 2))

/-- Direct exact clearance on one vertical side of a quadratic owner box. -/
private def directVerticalClearance (parameter : Gaussian) (box : Box)
    (x : Coordinate)
    (determinantNonzero :
      CCL.Riemann.SquareRootContinuationChain.Owner.verticalDeterminant
        parameter x ≠ 0) :
    RFAP.BoxClearance.VerticalLineClearance (rootPolynomial parameter) box x where
  bound := directVerticalClearanceBound parameter box x
  positive := RFAP.ConstructiveFraction.div_pos_direct
    (sq_pos_of_ne_zero determinantNonzero)
    (directLineMajorant_positive _ _ _ _)
  lower := by
    intro y lower upper
    let determinant :=
      CCL.Riemann.SquareRootContinuationChain.Owner.verticalDeterminant
        parameter x
    let realPart := x ^ 2 - y ^ 2 - parameter.re
    let imaginaryPart := 2 * x * y - parameter.im
    have coordinateSq : y ^ 2 ≤
        max (box.yLower ^ 2) (box.yUpper ^ 2) :=
      RFAP.Boxes.Box.sq_le_endpoint_max lower upper
    have identity : determinant =
        (4 * x ^ 2) * realPart +
          ((2 * x) * y + parameter.im) * imaginaryPart := by
      dsimp only [determinant, realPart, imaginaryPart,
        CCL.Riemann.SquareRootContinuationChain.Owner.verticalDeterminant]
      ring1
    have direct := directLineLower y
      (max (box.yLower ^ 2) (box.yUpper ^ 2))
      (4 * x ^ 2) (2 * x) parameter.im determinant realPart imaginaryPart
        coordinateSq identity
    have evaluation :
        RFAP.ConstructiveGaussian.Gaussian.normSq
            ((rootPolynomial parameter).eval (RFAP.Winding.point x y)) =
          (x ^ 2 - y ^ 2 - parameter.re) ^ 2 +
            (2 * x * y - parameter.im) ^ 2 := by
      simp [rootPolynomial, CCL.PowerMonodromy.polynomial_eval,
        CCL.Riemann.SquareRootSheets.degreeTwo_value, pow_two,
        RFAP.ConstructiveGaussian.Gaussian.normSq, RFAP.Winding.point]
      ring1
    rw [evaluation]
    dsimp only [determinant, realPart, imaginaryPart] at direct
    exact direct

/-- The executable lower bound used on one horizontal side of a quadratic
owner box. -/
def directHorizontalClearanceBound (parameter : Gaussian) (box : Box)
    (y : Coordinate) : Coordinate :=
  CCL.Riemann.SquareRootContinuationChain.Owner.horizontalDeterminant
      parameter y ^ 2 /
    directLineMajorant (4 * y ^ 2) (-(2 * y)) (-parameter.im)
      (max (box.xLower ^ 2) (box.xUpper ^ 2))

/-- Direct exact clearance on one horizontal side of a quadratic owner box. -/
private def directHorizontalClearance (parameter : Gaussian) (box : Box)
    (y : Coordinate)
    (determinantNonzero :
      CCL.Riemann.SquareRootContinuationChain.Owner.horizontalDeterminant
        parameter y ≠ 0) :
    RFAP.BoxClearance.HorizontalLineClearance (rootPolynomial parameter) box y where
  bound := directHorizontalClearanceBound parameter box y
  positive := RFAP.ConstructiveFraction.div_pos_direct
    (sq_pos_of_ne_zero determinantNonzero)
    (directLineMajorant_positive _ _ _ _)
  lower := by
    intro x lower upper
    let determinant :=
      CCL.Riemann.SquareRootContinuationChain.Owner.horizontalDeterminant
        parameter y
    let realPart := x ^ 2 - y ^ 2 - parameter.re
    let imaginaryPart := 2 * x * y - parameter.im
    have coordinateSq : x ^ 2 ≤
        max (box.xLower ^ 2) (box.xUpper ^ 2) :=
      RFAP.Boxes.Box.sq_le_endpoint_max lower upper
    have identity : determinant =
        (4 * y ^ 2) * realPart +
          ((-(2 * y)) * x + (-parameter.im)) * imaginaryPart := by
      dsimp only [determinant, realPart, imaginaryPart,
        CCL.Riemann.SquareRootContinuationChain.Owner.horizontalDeterminant]
      ring1
    have direct := directLineLower x
      (max (box.xLower ^ 2) (box.xUpper ^ 2))
      (4 * y ^ 2) (-(2 * y)) (-parameter.im) determinant realPart
        imaginaryPart coordinateSq identity
    have evaluation :
        RFAP.ConstructiveGaussian.Gaussian.normSq
            ((rootPolynomial parameter).eval (RFAP.Winding.point x y)) =
          (x ^ 2 - y ^ 2 - parameter.re) ^ 2 +
            (2 * x * y - parameter.im) ^ 2 := by
      simp [rootPolynomial, CCL.PowerMonodromy.polynomial_eval,
        CCL.Riemann.SquareRootSheets.degreeTwo_value, pow_two,
        RFAP.ConstructiveGaussian.Gaussian.normSq, RFAP.Winding.point]
      ring1
    rw [evaluation]
    dsimp only [determinant, realPart, imaginaryPart] at direct
    exact direct

/-- Direct quadratic boundary clearance using the four explicit side
resultants. -/
def directBoundaryClearance (parameter : Gaussian) (box : Box)
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
        parameter box.yUpper ≠ 0) :
    RFAP.BoxClearance.BoundaryClearance (rootPolynomial parameter) box :=
  RFAP.BoxClearance.boundaryOfLines
    (directVerticalClearance parameter box box.xLower leftNonzero)
    (directVerticalClearance parameter box box.xUpper rightNonzero)
    (directHorizontalClearance parameter box box.yLower bottomNonzero)
    (directHorizontalClearance parameter box box.yUpper topNonzero)

@[simp] theorem directBoundaryClearance_bound
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
        parameter box.yUpper ≠ 0) :
    (directBoundaryClearance parameter box leftNonzero rightNonzero
      bottomNonzero topNonzero).bound =
      min (directVerticalClearanceBound parameter box box.xLower)
        (min (directVerticalClearanceBound parameter box box.xUpper)
          (min (directHorizontalClearanceBound parameter box box.yLower)
            (directHorizontalClearanceBound parameter box box.yUpper))) := rfl

/-- A displayed rational value below all four direct side bounds is below the
cached quadratic boundary clearance. -/
theorem le_directBoundaryClearance_bound
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
    (lower : Coordinate)
    (leftLe : lower ≤ directVerticalClearanceBound parameter box box.xLower)
    (rightLe : lower ≤ directVerticalClearanceBound parameter box box.xUpper)
    (bottomLe :
      lower ≤ directHorizontalClearanceBound parameter box box.yLower)
    (topLe : lower ≤ directHorizontalClearanceBound parameter box box.yUpper) :
    lower ≤ (directBoundaryClearance parameter box leftNonzero rightNonzero
      bottomNonzero topNonzero).bound := by
  rw [directBoundaryClearance_bound]
  exact le_min leftLe (le_min rightLe (le_min bottomLe topLe))

/-- Cached lower and upper bounds for the exact four-resultant clearance of a
quadratic owner box.  Concrete examples can compute this finite record once
and reuse it through preparation and transport. -/
structure DirectBoundaryBounds (parameter : Gaussian) (box : Box)
    (lower upper : Coordinate) where
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
  lower_le : lower ≤
    (directBoundaryClearance parameter box leftNonzero rightNonzero
      bottomNonzero topNonzero).bound
  le_upper :
    (directBoundaryClearance parameter box leftNonzero rightNonzero
      bottomNonzero topNonzero).bound ≤ upper

/-- Assemble a direct-bound cache from the four exact side comparisons and
one upper comparison of their minimum. -/
theorem directBoundaryBoundsOfSideChecks
    (parameter : Gaussian) (box : Box) (lower upper : Coordinate)
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
    (leftLower : lower ≤
      directVerticalClearanceBound parameter box box.xLower)
    (rightLower : lower ≤
      directVerticalClearanceBound parameter box box.xUpper)
    (bottomLower : lower ≤
      directHorizontalClearanceBound parameter box box.yLower)
    (topLower : lower ≤
      directHorizontalClearanceBound parameter box box.yUpper)
    (upperBound :
      min (directVerticalClearanceBound parameter box box.xLower)
        (min (directVerticalClearanceBound parameter box box.xUpper)
          (min (directHorizontalClearanceBound parameter box box.yLower)
            (directHorizontalClearanceBound parameter box box.yUpper))) ≤
        upper) :
    DirectBoundaryBounds parameter box lower upper := by
  refine
    { leftNonzero := leftNonzero
      rightNonzero := rightNonzero
      bottomNonzero := bottomNonzero
      topNonzero := topNonzero
      lower_le := ?_
      le_upper := ?_ }
  · exact le_directBoundaryClearance_bound parameter box leftNonzero
      rightNonzero bottomNonzero topNonzero lower leftLower rightLower
        bottomLower topLower
  · rw [directBoundaryClearance_bound]
    exact upperBound

/-! The separated Sylvester eliminants used by the generic root refiner are
unnecessarily expensive for `Z² - parameter`: both axis resultants are the
displayed quartics already used by the direct boundary-clearance formulas.
Store those short polynomials directly, together with the existing explicit
Bézout certificates. -/

/-- The exact vertical-axis resultant of `Z² - parameter`. -/
def quadraticVerticalEliminant (parameter : Gaussian) : Polynomial :=
  ⟨[4, 0, -(4 * parameter.re), 0, -(parameter.im ^ 2)]⟩

/-- The exact horizontal-axis resultant of `Z² - parameter`. -/
def quadraticHorizontalEliminant (parameter : Gaussian) : Polynomial :=
  ⟨[-4, 0, -(4 * parameter.re), 0, parameter.im ^ 2]⟩

@[simp] theorem quadraticVerticalEliminant_eval
    (parameter : Gaussian) (x : Coordinate) :
    (quadraticVerticalEliminant parameter).eval x =
      CCL.Riemann.SquareRootContinuationChain.Owner.verticalDeterminant
        parameter x := by
  simp only [quadraticVerticalEliminant,
    RFAP.ComputablePolynomial.DensePolynomial.eval,
    RFAP.ComputablePolynomial.DensePolynomial.evalCoeffs,
    List.foldl_cons, List.foldl_nil]
  unfold CCL.Riemann.SquareRootContinuationChain.Owner.verticalDeterminant
  ring1

@[simp] theorem quadraticHorizontalEliminant_eval
    (parameter : Gaussian) (y : Coordinate) :
    (quadraticHorizontalEliminant parameter).eval y =
      CCL.Riemann.SquareRootContinuationChain.Owner.horizontalDeterminant
        parameter y := by
  simp only [quadraticHorizontalEliminant,
    RFAP.ComputablePolynomial.DensePolynomial.eval,
    RFAP.ComputablePolynomial.DensePolynomial.evalCoeffs,
    List.foldl_cons, List.foldl_nil]
  unfold CCL.Riemann.SquareRootContinuationChain.Owner.horizontalDeterminant
  ring1

/-- Constant-size axis-elimination data for the quadratic root polynomial.
This replaces the generic fraction-free Sylvester construction in every
subsequent refinement of a directly presented quadratic owner. -/
def quadraticAxisElimination (parameter : Gaussian) :
    RFAP.AxisSafeCuts.AxisEliminationCertificate
      (rootPolynomial parameter) 4 where
  vertical := quadraticVerticalEliminant parameter
  horizontal := quadraticHorizontalEliminant parameter
  vertical_nonzero := by
    change false = false
    rfl
  horizontal_nonzero := by
    change false = false
    rfl
  vertical_degree := by
    change 4 ≤ 4
    decide
  horizontal_degree := by
    change 4 ≤ 4
    decide
  vertical_coprime := by
    intro x nonzero
    apply CCL.Riemann.SquareRootContinuationChain.Owner.verticalCoprime
      parameter x
    rw [← quadraticVerticalEliminant_eval]
    exact nonzero
  horizontal_coprime := by
    intro y nonzero
    apply CCL.Riemann.SquareRootContinuationChain.Owner.horizontalCoprime
      parameter y
    rw [← quadraticHorizontalEliminant_eval]
    exact nonzero

private def midpoint (lower upper : Coordinate) : Coordinate :=
  (lower + upper) / 2

private theorem midpoint_strict {lower upper : Coordinate}
    (proper : lower < upper) :
    lower < midpoint lower upper ∧ midpoint lower upper < upper := by
  constructor
  · apply (RFAP.ConstructiveFraction.lt_div_iff_pos
      (by decide : (0 : Coordinate) < 2)).2
    calc
      lower * 2 = lower + lower := by ring1
      _ < lower + upper :=
        RFAP.ConstructiveFraction.add_lt_add_left_direct proper lower
  · apply (RFAP.ConstructiveFraction.div_lt_iff_pos
      (by decide : (0 : Coordinate) < 2)).2
    calc
      lower + upper < upper + upper :=
        RFAP.ConstructiveFraction.add_lt_add_right_direct proper upper
      _ = upper * 2 := by ring1

private def insetLower (lower upper : Coordinate) : Coordinate :=
  midpoint lower
    (midpoint lower (midpoint lower (midpoint lower upper)))

private def insetUpper (lower upper : Coordinate) : Coordinate :=
  midpoint
    (midpoint (midpoint (midpoint lower upper) upper) upper) upper

private theorem insetLower_strict {lower upper : Coordinate}
    (proper : lower < upper) :
    lower < insetLower lower upper ∧
      insetLower lower upper < midpoint lower upper := by
  let half := midpoint lower upper
  let quarter := midpoint lower half
  let eighth := midpoint lower quarter
  have lowerHalf := midpoint_strict proper
  have lowerQuarter := midpoint_strict lowerHalf.1
  have lowerEighth := midpoint_strict lowerQuarter.1
  have lowerSixteenth := midpoint_strict lowerEighth.1
  exact ⟨lowerSixteenth.1,
    lowerSixteenth.2.trans
      (lowerEighth.2.trans lowerQuarter.2)⟩

private theorem insetUpper_strict {lower upper : Coordinate}
    (proper : lower < upper) :
    midpoint lower upper < insetUpper lower upper ∧
      insetUpper lower upper < upper := by
  let half := midpoint lower upper
  let threeQuarter := midpoint half upper
  let sevenEighth := midpoint threeQuarter upper
  have halfUpper := midpoint_strict proper
  have quarterUpper := midpoint_strict halfUpper.2
  have eighthUpper := midpoint_strict quarterUpper.2
  have sixteenthUpper := midpoint_strict eighthUpper.2
  exact ⟨quarterUpper.1.trans
      (eighthUpper.1.trans sixteenthUpper.1),
    sixteenthUpper.2⟩

/-- A fixed strict inset, retaining fifteen sixteenths of each coordinate
interval.  Its winding is checked before it is used as a fast refinement
source. -/
private def strictInsetBox (box : Box) (proper : box.Proper) : Box where
  xLower := insetLower box.xLower box.xUpper
  xUpper := insetUpper box.xLower box.xUpper
  yLower := insetLower box.yLower box.yUpper
  yUpper := insetUpper box.yLower box.yUpper
  x_valid := ((insetLower_strict proper.1).2.trans
    (insetUpper_strict proper.1).1).le
  y_valid := ((insetLower_strict proper.2).2.trans
    (insetUpper_strict proper.2).1).le

private theorem strictInsetBox_strict (box : Box) (proper : box.Proper) :
    (strictInsetBox box proper).StrictInterior box :=
  ⟨(insetLower_strict proper.1).1, (insetUpper_strict proper.1).2,
    (insetLower_strict proper.2).1, (insetUpper_strict proper.2).2⟩

private theorem strictInsetBox_proper (box : Box) (proper : box.Proper) :
    (strictInsetBox box proper).Proper :=
  ⟨(insetLower_strict proper.1).2.trans (insetUpper_strict proper.1).1,
    (insetLower_strict proper.2).2.trans (insetUpper_strict proper.2).1⟩

private structure StrictInsetData {parameter : Gaussian} {ambient : Box}
    (current : RFAP.ShrinkingTrack.WindingOneState
      (rootPolynomial parameter) ambient) where
  box : Box
  strict : box.StrictInterior current.box
  proper : box.Proper

/-- A much narrower strict inset whose margin is a finite dyadic number below
the current protected-boundary radius.  Keeping the displayed margin dyadic
prevents repeated strict-nesting requests from copying the full exact
clearance denominator into all four box coordinates. -/
private def protectedStrictInset {parameter : Gaussian} {ambient : Box}
    (current : RFAP.ShrinkingTrack.WindingOneState
      (rootPolynomial parameter) ambient) : StrictInsetData current := by
  let safeRadius := RFAP.ProtectedBoundary.protectedBoundaryRadius
    (rootPolynomial parameter) current.box current.clearance
  have safeRadiusPositive : 0 < safeRadius :=
    RFAP.ProtectedBoundary.protectedBoundaryRadius_pos
      (rootPolynomial parameter) current.clearance current.proper
  let rho := CCL.FiniteGeometric.quarterRadius 1
    (CCL.FiniteGeometric.firstQuarterBelow 1 0 safeRadius)
  have rhoPositive : 0 < rho :=
    CCL.FiniteGeometric.quarterRadius_pos (by decide) _
  have rhoLeSafeRadius : rho ≤ safeRadius := by
    exact (CCL.FiniteGeometric.firstQuarterBelow_accurate 1 (by decide) 0
      safeRadius safeRadiusPositive).le
  have widthBounds :=
    RFAP.ProtectedBoundary.protectedBoundaryRadius_le_widths
      (rootPolynomial parameter) current.box current.clearance
  have safeScaledX : safeRadius * 16 ≤ current.box.widthX :=
    (RFAP.ConstructiveFraction.le_div_iff_pos
      (show (0 : Coordinate) < 16 by decide)).mp widthBounds.1
  have safeScaledY : safeRadius * 16 ≤ current.box.widthY :=
    (RFAP.ConstructiveFraction.le_div_iff_pos
      (show (0 : Coordinate) < 16 by decide)).mp widthBounds.2
  have scaledX : rho * 16 ≤ current.box.widthX :=
    (RFAP.ConstructiveFraction.mul_le_mul_of_nonneg_right_direct
      rhoLeSafeRadius (by decide)).trans safeScaledX
  have scaledY : rho * 16 ≤ current.box.widthY :=
    (RFAP.ConstructiveFraction.mul_le_mul_of_nonneg_right_direct
      rhoLeSafeRadius (by decide)).trans safeScaledY
  have twiceX : 2 * rho < current.box.widthX := by
    calc
      2 * rho < 16 * rho :=
        RFAP.ConstructiveFraction.mul_lt_mul_of_pos_right_direct
          (by decide) rhoPositive
      _ = rho * 16 := by ring1
      _ ≤ current.box.widthX := scaledX
  have twiceY : 2 * rho < current.box.widthY := by
    calc
      2 * rho < 16 * rho :=
        RFAP.ConstructiveFraction.mul_lt_mul_of_pos_right_direct
          (by decide) rhoPositive
      _ = rho * 16 := by ring1
      _ ≤ current.box.widthY := scaledY
  have xProper : current.box.xLower + rho < current.box.xUpper - rho := by
    apply RFAP.ConstructiveFraction.lt_of_add_lt_add_right_direct (c := rho)
    calc
      current.box.xLower + rho + rho =
          current.box.xLower + 2 * rho := by ring1
      _ < current.box.xLower + current.box.widthX :=
        RFAP.ConstructiveFraction.add_lt_add_left_direct twiceX _
      _ = current.box.xUpper := by
        unfold RFAP.Boxes.Box.widthX
        ring1
      _ = current.box.xUpper - rho + rho := by ring1
  have yProper : current.box.yLower + rho < current.box.yUpper - rho := by
    apply RFAP.ConstructiveFraction.lt_of_add_lt_add_right_direct (c := rho)
    calc
      current.box.yLower + rho + rho =
          current.box.yLower + 2 * rho := by ring1
      _ < current.box.yLower + current.box.widthY :=
        RFAP.ConstructiveFraction.add_lt_add_left_direct twiceY _
      _ = current.box.yUpper := by
        unfold RFAP.Boxes.Box.widthY
        ring1
      _ = current.box.yUpper - rho + rho := by ring1
  let box : Box :=
    { xLower := current.box.xLower + rho
      xUpper := current.box.xUpper - rho
      yLower := current.box.yLower + rho
      yUpper := current.box.yUpper - rho
      x_valid := xProper.le
      y_valid := yProper.le }
  have left : current.box.xLower < box.xLower := by
    exact lt_add_of_pos_right current.box.xLower rhoPositive
  have right : box.xUpper < current.box.xUpper := by
    exact sub_lt_self current.box.xUpper rhoPositive
  have bottom : current.box.yLower < box.yLower := by
    exact lt_add_of_pos_right current.box.yLower rhoPositive
  have top : box.yUpper < current.box.yUpper := by
    exact sub_lt_self current.box.yUpper rhoPositive
  exact
    { box := box
      strict := ⟨left, right, bottom, top⟩
      proper := ⟨xProper, yProper⟩ }

/-- Proof-bearing result of the direct quadratic refinement attempt. -/
private structure FastRefinement {parameter : Gaussian} {ambient : Box}
    (current : RFAP.ShrinkingTrack.WindingOneState
      (rootPolynomial parameter) ambient)
    (epsilon : Coordinate) where
  state : RFAP.ShrinkingTrack.WindingOneState
    (rootPolynomial parameter) ambient
  nested : state.box.Refines current.box
  strict : state.box.StrictInterior current.box
  accurate : state.box.diagonalSq ≤ epsilon ^ 2

/-- The direct raw-subdivision target is exactly the caller's requested
squared diameter.  Strict nesting is checked separately, first on the raw
candidate and then through one of the certified inset sources. -/
private def fastRefinementTarget {parameter : Gaussian} {ambient : Box}
    (_current : RFAP.ShrinkingTrack.WindingOneState
      (rootPolynomial parameter) ambient)
    (epsilon : Coordinate) : Coordinate :=
  epsilon ^ 2

private theorem fastRefinementTarget_positive {parameter : Gaussian}
    {ambient : Box}
    (current : RFAP.ShrinkingTrack.WindingOneState
      (rootPolynomial parameter) ambient)
    {epsilon : Coordinate} (positive : 0 < epsilon) :
    0 < fastRefinementTarget current epsilon := by
  unfold fastRefinementTarget
  exact RFAP.ConstructiveFraction.pow_pos_direct positive 2

private structure StrictRawInset {parameter : Gaussian} {ambient : Box}
    (current : RFAP.ShrinkingTrack.WindingOneState
      (rootPolynomial parameter) ambient) where
  state : RFAP.RawSubdivision.RawWindingState
    (rootPolynomial parameter) ambient
  strict : state.box.StrictInterior current.box

/-- Check one supplied strict inset and retain it only when its four sides are
root-free and its winding is the selected quadratic occurrence. -/
private def checkedRawInset? {parameter : Gaussian} {ambient : Box}
    (current : RFAP.ShrinkingTrack.WindingOneState
      (rootPolynomial parameter) ambient)
    (inset : StrictInsetData current) :
    Option (StrictRawInset current) := by
  let box := inset.box
  if leftNonzero :
      CCL.Riemann.SquareRootContinuationChain.Owner.verticalDeterminant
        parameter box.xLower ≠ 0 then
    if rightNonzero :
        CCL.Riemann.SquareRootContinuationChain.Owner.verticalDeterminant
          parameter box.xUpper ≠ 0 then
      if bottomNonzero :
          CCL.Riemann.SquareRootContinuationChain.Owner.horizontalDeterminant
            parameter box.yLower ≠ 0 then
        if topNonzero :
            CCL.Riemann.SquareRootContinuationChain.Owner.horizontalDeterminant
              parameter box.yUpper ≠ 0 then
          if windingFour : RFAP.Winding.quadrupledBoxWinding
              (rootPolynomial parameter) box = 4 then
            exact some
              { state :=
                  { box := box
                    refinesAmbient := inset.strict.refines.trans
                      current.refinesAmbient
                    proper := inset.proper
                    clearance := directBoundaryClearance parameter box
                      leftNonzero rightNonzero bottomNonzero topNonzero
                    rawWinding_ne := by
                      rw [windingFour]
                      decide }
                strict := inset.strict }
          else exact none
        else exact none
      else exact none
    else exact none
  else exact none

/-- Check the cheap fixed inset first, then retry with the much narrower
clearance-scaled inset.  Failure remains harmless because the caller retains
its total generic fallback. -/
private def strictRawInset? {parameter : Gaussian} {ambient : Box}
    (current : RFAP.ShrinkingTrack.WindingOneState
      (rootPolynomial parameter) ambient) :
    Option (StrictRawInset current) :=
  let fixed : StrictInsetData current :=
    { box := strictInsetBox current.box current.proper
      strict := strictInsetBox_strict current.box current.proper
      proper := strictInsetBox_proper current.box current.proper }
  match checkedRawInset? current fixed with
  | some inset => some inset
  | none => checkedRawInset? current (protectedStrictInset current)

/-- Recheck a raw quadratic candidate and promote it to the complete strict
track-state interface. -/
private def checkedFastRefinement? {parameter : Gaussian} {ambient : Box}
    (current : RFAP.ShrinkingTrack.WindingOneState
      (rootPolynomial parameter) ambient)
    (epsilon : Coordinate)
    (candidate : RFAP.RawSubdivision.RawWindingState
      (rootPolynomial parameter) ambient)
    (strict : candidate.box.StrictInterior current.box)
    (accurate : candidate.box.diagonalSq ≤ epsilon ^ 2) :
    Option (FastRefinement current epsilon) := by
  if leftNonzero :
      CCL.Riemann.SquareRootContinuationChain.Owner.verticalDeterminant
        parameter candidate.box.xLower ≠ 0 then
    if rightNonzero :
        CCL.Riemann.SquareRootContinuationChain.Owner.verticalDeterminant
          parameter candidate.box.xUpper ≠ 0 then
      if bottomNonzero :
          CCL.Riemann.SquareRootContinuationChain.Owner.horizontalDeterminant
            parameter candidate.box.yLower ≠ 0 then
        if topNonzero :
            CCL.Riemann.SquareRootContinuationChain.Owner.horizontalDeterminant
              parameter candidate.box.yUpper ≠ 0 then
          if windingFour : RFAP.Winding.quadrupledBoxWinding
              (rootPolynomial parameter) candidate.box = 4 then
            let clearance := directBoundaryClearance parameter candidate.box
              leftNonzero rightNonzero bottomNonzero topNonzero
            let state : RFAP.ShrinkingTrack.WindingOneState
                (rootPolynomial parameter) ambient :=
              { box := candidate.box
                refinesAmbient := candidate.refinesAmbient
                proper := candidate.proper
                clearance := clearance
                rawWindingFour := windingFour
                ambientLeftClearance :=
                  directVerticalClearance parameter ambient
                    candidate.box.xLower leftNonzero
                ambientRightClearance :=
                  directVerticalClearance parameter ambient
                    candidate.box.xUpper rightNonzero
                ambientBottomClearance :=
                  directHorizontalClearance parameter ambient
                    candidate.box.yLower bottomNonzero
                ambientTopClearance :=
                  directHorizontalClearance parameter ambient
                    candidate.box.yUpper topNonzero }
            exact some
              { state := state
                nested := strict.refines
                strict := strict
                accurate := accurate }
          else exact none
        else exact none
      else exact none
    else exact none
  else exact none

/-- Try the much cheaper direct quadratic subdivision before invoking the
generic Newton-band fallback.  Every successful branch rechecks all four
global side resultants and winding four, so the returned track state has the
same full interface as the generic extractor. -/
private def fastRefinement? {parameter : Gaussian} {ambient : Box}
    (current : RFAP.ShrinkingTrack.WindingOneState
      (rootPolynomial parameter) ambient)
    (epsilon : Coordinate) (positive : 0 < epsilon) :
    Option (FastRefinement current epsilon) := by
  let initial := current.raw
  let target := fastRefinementTarget current epsilon
  let candidate := RFAP.RawSubdivision.refineTo
    (quadraticAxisElimination parameter) initial target
  have candidateAccurate : candidate.box.diagonalSq ≤ epsilon ^ 2 :=
    RFAP.RawSubdivision.refineTo_diagonalSq_le
      (quadraticAxisElimination parameter) initial
      (fastRefinementTarget_positive current positive)
  if strict : candidate.box.StrictInterior current.box then
    exact checkedFastRefinement? current epsilon candidate strict
      candidateAccurate
  else
    match strictRawInset? current with
    | none => exact none
    | some inset =>
        let insetCandidate := RFAP.RawSubdivision.refineTo
          (quadraticAxisElimination parameter) inset.state target
        have insetRefines : insetCandidate.box.Refines inset.state.box :=
          RFAP.RawSubdivision.refineTo_refines
            (quadraticAxisElimination parameter) inset.state target
        have insetStrict : insetCandidate.box.StrictInterior current.box :=
          inset.strict.of_refines insetRefines
        have insetAccurate : insetCandidate.box.diagonalSq ≤ epsilon ^ 2 :=
          RFAP.RawSubdivision.refineTo_diagonalSq_le
            (quadraticAxisElimination parameter) inset.state
            (fastRefinementTarget_positive current positive)
        exact checkedFastRefinement? current epsilon insetCandidate insetStrict
          insetAccurate

/-! A transported owner normally uses only its displayed initial state on the
next prepared edge.  Building `ShrinkingTrack.ofInitial` eagerly evaluates the
quadratic eliminant captured by its refinement closure, even when no
refinement is requested.  The following extensionally identical constructor
puts that finite computation inside the closure instead. -/

private def deferredRefine {parameter : Gaussian}
    (parameterNonzero : parameter ≠ 0) {ambient : Box}
    (current : RFAP.ShrinkingTrack.WindingOneState
      (rootPolynomial parameter) ambient)
    (epsilon : Coordinate) (positive : 0 < epsilon) :
    RFAP.ShrinkingTrack.WindingOneState
      (rootPolynomial parameter) ambient :=
  match fastRefinement? current epsilon positive with
  | some fast => fast.state
  | none =>
      RFAP.ShrinkingTrack.refineState
        (by
          unfold rootPolynomial
          rw [CCL.PowerMonodromy.polynomial_degree]
          exact CCL.Riemann.SquareRootSheets.degreeTwo_atLeastTwo)
        (by
          unfold rootPolynomial
          exact CCL.PowerMonodromy.squarefree parameterNonzero
            CCL.Riemann.SquareRootSheets.degreeTwo)
        (quadraticAxisElimination parameter)
        current epsilon positive

private theorem deferredRefine_refines {parameter : Gaussian}
    (parameterNonzero : parameter ≠ 0) {ambient : Box}
    (current : RFAP.ShrinkingTrack.WindingOneState
      (rootPolynomial parameter) ambient)
    (epsilon : Coordinate) (positive : 0 < epsilon) :
    (deferredRefine parameterNonzero current epsilon positive).box.Refines
      current.box := by
  unfold deferredRefine
  generalize attempt : fastRefinement? current epsilon positive = result
  cases result with
  | none => exact RFAP.ShrinkingTrack.refineState_refines _ _ _ _ _ _
  | some fast => exact fast.nested

private theorem deferredRefine_strict {parameter : Gaussian}
    (parameterNonzero : parameter ≠ 0) {ambient : Box}
    (current : RFAP.ShrinkingTrack.WindingOneState
      (rootPolynomial parameter) ambient)
    (epsilon : Coordinate) (positive : 0 < epsilon) :
    (deferredRefine parameterNonzero current epsilon positive).box.StrictInterior
      current.box := by
  unfold deferredRefine
  generalize attempt : fastRefinement? current epsilon positive = result
  cases result with
  | none => exact RFAP.ShrinkingTrack.refineState_strict _ _ _ _ _ _
  | some fast => exact fast.strict

private theorem deferredRefine_accurate {parameter : Gaussian}
    (parameterNonzero : parameter ≠ 0) {ambient : Box}
    (current : RFAP.ShrinkingTrack.WindingOneState
      (rootPolynomial parameter) ambient)
    (epsilon : Coordinate) (positive : 0 < epsilon) :
    (deferredRefine parameterNonzero current epsilon positive).box.diagonalSq ≤
      epsilon ^ 2 := by
  unfold deferredRefine
  generalize attempt : fastRefinement? current epsilon positive = result
  cases result with
  | none => exact RFAP.ShrinkingTrack.refineState_accurate _ _ _ _ _ _
  | some fast => exact fast.accurate

private def deferredTrack {parameter : Gaussian}
    (parameterNonzero : parameter ≠ 0) {ambient : Box}
    (initial : RFAP.ShrinkingTrack.WindingOneState
      (rootPolynomial parameter) ambient) :
    RFAP.ShrinkingTrack.WindingOneTrack
      (rootPolynomial parameter) ambient where
  initial := initial
  refine := deferredRefine parameterNonzero
  nested := deferredRefine_refines parameterNonzero
  strict := deferredRefine_strict parameterNonzero
  accurate := deferredRefine_accurate parameterNonzero

private def ownerOfState {parameter : Gaussian}
    (parameterNonzero : parameter ≠ 0) {ambient : Box}
    (initial : RFAP.ShrinkingTrack.WindingOneState
      (rootPolynomial parameter) ambient) : Owner parameter where
  parameterNonzero := parameterNonzero
  ambient := ambient
  track := deferredTrack parameterNonzero initial

private def childState {parameter : Gaussian} (source : Owner parameter)
    (child : Box) (childRefines : child.Refines source.track.initial.box)
    (childProper : child.Proper)
    (clearance : RFAP.BoxClearance.BoundaryClearance
      (rootPolynomial parameter) child)
    (windingFour : RFAP.Winding.quadrupledBoxWinding
      (rootPolynomial parameter) child = 4)
    (left : RFAP.BoxClearance.VerticalLineClearance
      (rootPolynomial parameter) source.track.initial.box child.xLower)
    (right : RFAP.BoxClearance.VerticalLineClearance
      (rootPolynomial parameter) source.track.initial.box child.xUpper)
    (bottom : RFAP.BoxClearance.HorizontalLineClearance
      (rootPolynomial parameter) source.track.initial.box child.yLower)
    (top : RFAP.BoxClearance.HorizontalLineClearance
      (rootPolynomial parameter) source.track.initial.box child.yUpper) :
    RFAP.ShrinkingTrack.WindingOneState
      (rootPolynomial parameter) source.track.initial.box where
  box := child
  refinesAmbient := childRefines
  proper := childProper
  clearance := clearance
  rawWindingFour := windingFour
  ambientLeftClearance := left
  ambientRightClearance := right
  ambientBottomClearance := bottom
  ambientTopClearance := top

/-- Construct a quadratic owner whose initial state uses the direct
resultant formula from the outset. -/
def directOwnerOfBox (parameter : Gaussian) (parameterNonzero : parameter ≠ 0)
    (box : Box) (proper : box.Proper)
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
    (windingFour : RFAP.Winding.quadrupledBoxWinding
      (rootPolynomial parameter) box = 4) : Owner parameter :=
  let clearance := directBoundaryClearance parameter box leftNonzero
    rightNonzero bottomNonzero topNonzero
  let initial : RFAP.ShrinkingTrack.WindingOneState
      (rootPolynomial parameter) box :=
    { box := box
      refinesAmbient := RFAP.Boxes.Box.refines_refl box
      proper := proper
      clearance := clearance
      rawWindingFour := windingFour
      ambientLeftClearance := RFAP.BoxClearance.leftOfBoundary clearance
      ambientRightClearance := RFAP.BoxClearance.rightOfBoundary clearance
      ambientBottomClearance := RFAP.BoxClearance.bottomOfBoundary clearance
      ambientTopClearance := RFAP.BoxClearance.topOfBoundary clearance }
  { parameterNonzero := parameterNonzero
    ambient := box
    track := deferredTrack parameterNonzero initial }

@[simp] theorem directOwnerOfBox_initial_box
    (parameter : Gaussian) (parameterNonzero : parameter ≠ 0)
    (box : Box) (proper : box.Proper)
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
    (windingFour : RFAP.Winding.quadrupledBoxWinding
      (rootPolynomial parameter) box = 4) :
    (directOwnerOfBox parameter parameterNonzero box proper leftNonzero
      rightNonzero bottomNonzero topNonzero windingFour).track.initial.box =
        box := rfl

@[simp] theorem directOwnerOfBox_ambient
    (parameter : Gaussian) (parameterNonzero : parameter ≠ 0)
    (box : Box) (proper : box.Proper)
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
    (windingFour : RFAP.Winding.quadrupledBoxWinding
      (rootPolynomial parameter) box = 4) :
    (directOwnerOfBox parameter parameterNonzero box proper leftNonzero
      rightNonzero bottomNonzero topNonzero windingFour).ambient = box := rfl

@[simp] theorem directOwnerOfBox_initial_clearance_bound
    (parameter : Gaussian) (parameterNonzero : parameter ≠ 0)
    (box : Box) (proper : box.Proper)
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
    (windingFour : RFAP.Winding.quadrupledBoxWinding
      (rootPolynomial parameter) box = 4) :
    (directOwnerOfBox parameter parameterNonzero box proper leftNonzero
      rightNonzero bottomNonzero topNonzero windingFour).track.initial.clearance.bound =
        (directBoundaryClearance parameter box leftNonzero rightNonzero
          bottomNonzero topNonzero).bound := rfl

/-- A directly presented quadratic owner stores the same boundary bound on
each ambient side. -/
theorem directOwnerOfBox_ambientClearanceDominance
    (parameter : Gaussian) (parameterNonzero : parameter ≠ 0)
    (box : Box) (proper : box.Proper)
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
    (windingFour : RFAP.Winding.quadrupledBoxWinding
      (rootPolynomial parameter) box = 4) :
    AmbientClearanceDominance
      (directOwnerOfBox parameter parameterNonzero box proper leftNonzero
        rightNonzero bottomNonzero topNonzero windingFour) := by
  exact ⟨le_rfl, le_rfl, le_rfl, le_rfl⟩

/-- Midpoint split using the quadratic side resultants directly, with no
Sylvester eliminant construction. -/
private def midpointGrid (parameter : Gaussian) (box : Box)
    (proper : box.Proper)
    (verticalNonzero :
      CCL.Riemann.SquareRootContinuationChain.Owner.verticalDeterminant
        parameter (midpoint box.xLower box.xUpper) ≠ 0)
    (horizontalNonzero :
      CCL.Riemann.SquareRootContinuationChain.Owner.horizontalDeterminant
        parameter (midpoint box.yLower box.yUpper) ≠ 0) :
    RFAP.AxisSafeCuts.ClearFourGrid (rootPolynomial parameter) box where
  xCut := midpoint box.xLower box.xUpper
  yCut := midpoint box.yLower box.yUpper
  xInside := ⟨(midpoint_strict proper.1).1.le,
    (midpoint_strict proper.1).2.le⟩
  yInside := ⟨(midpoint_strict proper.2).1.le,
    (midpoint_strict proper.2).2.le⟩
  verticalClearance := directVerticalClearance parameter box _ verticalNonzero
  horizontalClearance :=
    directHorizontalClearance parameter box _ horizontalNonzero

private def leftShiftLower (lower _upper : Coordinate) : Coordinate :=
  lower

private def leftShiftUpper (lower upper : Coordinate) : Coordinate :=
  midpoint (midpoint (midpoint lower upper) upper) upper

private def rightShiftLower (lower upper : Coordinate) : Coordinate :=
  midpoint lower (midpoint lower (midpoint lower upper))

private def rightShiftUpper (_lower upper : Coordinate) : Coordinate :=
  upper

private theorem leftShift_proper {lower upper : Coordinate}
    (proper : lower < upper) :
    leftShiftLower lower upper < leftShiftUpper lower upper := by
  exact (midpoint_strict proper).1.trans
    ((midpoint_strict (midpoint_strict proper).2).1.trans
      (midpoint_strict
        (midpoint_strict (midpoint_strict proper).2).2).1)

private theorem rightShift_proper {lower upper : Coordinate}
    (proper : lower < upper) :
    rightShiftLower lower upper < rightShiftUpper lower upper := by
  exact
    ((midpoint_strict
      (midpoint_strict (midpoint_strict proper).1).1).2.trans
        (midpoint_strict (midpoint_strict proper).1).2).trans
      (midpoint_strict proper).2

private theorem leftShiftLower_le {lower upper : Coordinate}
    (_valid : lower ≤ upper) : leftShiftLower lower upper ≤ lower := by
  exact le_rfl

private theorem midpoint_le_leftShiftUpper {lower upper : Coordinate}
    (proper : lower < upper) : midpoint lower upper ≤
      leftShiftUpper lower upper := by
  exact ((midpoint_strict (midpoint_strict proper).2).1.trans
    (midpoint_strict
      (midpoint_strict (midpoint_strict proper).2).2).1).le

private theorem rightShiftLower_le_midpoint {lower upper : Coordinate}
    (proper : lower < upper) : rightShiftLower lower upper ≤
      midpoint lower upper := by
  exact ((midpoint_strict
    (midpoint_strict (midpoint_strict proper).1).1).2.trans
      (midpoint_strict (midpoint_strict proper).1).2).le

private theorem upper_le_rightShiftUpper {lower upper : Coordinate}
    (_valid : lower ≤ upper) : upper ≤ rightShiftUpper lower upper := by
  exact le_rfl

private theorem leftShiftUpper_le {lower upper : Coordinate}
    (proper : lower < upper) : leftShiftUpper lower upper ≤ upper := by
  exact (midpoint_strict
    (midpoint_strict (midpoint_strict proper).2).2).2.le

private theorem lower_le_rightShiftLower {lower upper : Coordinate}
    (proper : lower < upper) : lower ≤ rightShiftLower lower upper := by
  exact (midpoint_strict
    (midpoint_strict (midpoint_strict proper).1).1).1.le

private def shiftedLowerLeft (box : Box) (proper : box.Proper) : Box where
  xLower := leftShiftLower box.xLower box.xUpper
  xUpper := leftShiftUpper box.xLower box.xUpper
  yLower := leftShiftLower box.yLower box.yUpper
  yUpper := leftShiftUpper box.yLower box.yUpper
  x_valid := (leftShift_proper proper.1).le
  y_valid := (leftShift_proper proper.2).le

private def shiftedUpperLeft (box : Box) (proper : box.Proper) : Box where
  xLower := leftShiftLower box.xLower box.xUpper
  xUpper := leftShiftUpper box.xLower box.xUpper
  yLower := rightShiftLower box.yLower box.yUpper
  yUpper := rightShiftUpper box.yLower box.yUpper
  x_valid := (leftShift_proper proper.1).le
  y_valid := (rightShift_proper proper.2).le

private def shiftedLowerRight (box : Box) (proper : box.Proper) : Box where
  xLower := rightShiftLower box.xLower box.xUpper
  xUpper := rightShiftUpper box.xLower box.xUpper
  yLower := leftShiftLower box.yLower box.yUpper
  yUpper := leftShiftUpper box.yLower box.yUpper
  x_valid := (rightShift_proper proper.1).le
  y_valid := (leftShift_proper proper.2).le

private def shiftedUpperRight (box : Box) (proper : box.Proper) : Box where
  xLower := rightShiftLower box.xLower box.xUpper
  xUpper := rightShiftUpper box.xLower box.xUpper
  yLower := rightShiftLower box.yLower box.yUpper
  yUpper := rightShiftUpper box.yLower box.yUpper
  x_valid := (rightShift_proper proper.1).le
  y_valid := (rightShift_proper proper.2).le

private structure DirectBoxOwner (parameter : Gaussian) (box : Box) where
  owner : Owner parameter
  initialBox : owner.track.initial.box = box
  ambientBox : owner.ambient = box
  dominance : AmbientClearanceDominance owner
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
  initialClearanceBound : owner.track.initial.clearance.bound =
    (directBoundaryClearance parameter box leftNonzero rightNonzero
      bottomNonzero topNonzero).bound
  ambientLeftClearanceBound :
    owner.track.initial.ambientLeftClearance.bound =
      (directBoundaryClearance parameter box leftNonzero rightNonzero
        bottomNonzero topNonzero).bound

private def directOwnerOnBox? (parameter : Gaussian)
    (parameterNonzero : parameter ≠ 0) (box : Box) (proper : box.Proper) :
    Option (DirectBoxOwner parameter box) :=
  if leftNonzero :
      CCL.Riemann.SquareRootContinuationChain.Owner.verticalDeterminant
        parameter box.xLower ≠ 0 then
    if rightNonzero :
        CCL.Riemann.SquareRootContinuationChain.Owner.verticalDeterminant
          parameter box.xUpper ≠ 0 then
      if bottomNonzero :
          CCL.Riemann.SquareRootContinuationChain.Owner.horizontalDeterminant
            parameter box.yLower ≠ 0 then
        if topNonzero :
            CCL.Riemann.SquareRootContinuationChain.Owner.horizontalDeterminant
              parameter box.yUpper ≠ 0 then
          if windingFour : (RFAP.Winding.quadrupledBoxWinding
              (rootPolynomial parameter) box = 4) then
            some
              { owner := directOwnerOfBox parameter parameterNonzero box proper
                  leftNonzero rightNonzero bottomNonzero topNonzero windingFour
                initialBox := directOwnerOfBox_initial_box parameter
                  parameterNonzero box proper leftNonzero rightNonzero
                    bottomNonzero topNonzero windingFour
                ambientBox := directOwnerOfBox_ambient parameter parameterNonzero
                  box proper leftNonzero rightNonzero bottomNonzero topNonzero
                    windingFour
                dominance := directOwnerOfBox_ambientClearanceDominance parameter
                  parameterNonzero box proper leftNonzero rightNonzero
                    bottomNonzero topNonzero windingFour
                leftNonzero := leftNonzero
                rightNonzero := rightNonzero
                bottomNonzero := bottomNonzero
                topNonzero := topNonzero
                initialClearanceBound :=
                  directOwnerOfBox_initial_clearance_bound parameter
                    parameterNonzero box proper leftNonzero rightNonzero
                      bottomNonzero topNonzero windingFour
                ambientLeftClearanceBound := rfl }
          else none
        else none
      else none
    else none
  else none

/-- A directly certified owner in one midpoint child of the parent box. -/
structure DirectRecenter (parameter : Gaussian) (parent : Box) where
  owner : Owner parameter
  refines : owner.track.initial.box.Refines parent

/-- Try the four midpoint children in fixed finite order and retain the unique
winding-four child as a freshly centred quadratic owner. -/
def midpointRecenter? (parameter : Gaussian) (parameterNonzero : parameter ≠ 0)
    (box : Box) (proper : box.Proper) :
    Option (DirectRecenter parameter box) := by
  let xCut := midpoint box.xLower box.xUpper
  let yCut := midpoint box.yLower box.yUpper
  if xNonzero :
      CCL.Riemann.SquareRootContinuationChain.Owner.verticalDeterminant
        parameter xCut ≠ 0 then
    if yNonzero :
        CCL.Riemann.SquareRootContinuationChain.Owner.horizontalDeterminant
          parameter yCut ≠ 0 then
      let grid := midpointGrid parameter box proper xNonzero yNonzero
      if lowerLeftWinding : (RFAP.Winding.quadrupledBoxWinding
          (rootPolynomial parameter) grid.lowerLeft = 4) then
        let candidate := grid.lowerLeft
        match directOwnerOnBox? parameter parameterNonzero candidate
            ⟨(midpoint_strict proper.1).1, (midpoint_strict proper.2).1⟩ with
        | none => exact none
        | some shifted =>
            exact some
              { owner := shifted.owner
                refines := by
                  rw [shifted.initialBox]
                  exact grid.lowerLeft_refines }
      else if upperLeftWinding : (RFAP.Winding.quadrupledBoxWinding
          (rootPolynomial parameter) grid.upperLeft = 4) then
        let candidate := grid.upperLeft
        match directOwnerOnBox? parameter parameterNonzero candidate
            ⟨(midpoint_strict proper.1).1, (midpoint_strict proper.2).2⟩ with
        | none => exact none
        | some shifted =>
            exact some
              { owner := shifted.owner
                refines := by
                  rw [shifted.initialBox]
                  exact grid.upperLeft_refines }
      else if lowerRightWinding : (RFAP.Winding.quadrupledBoxWinding
          (rootPolynomial parameter) grid.lowerRight = 4) then
        let candidate := grid.lowerRight
        match directOwnerOnBox? parameter parameterNonzero candidate
            ⟨(midpoint_strict proper.1).2, (midpoint_strict proper.2).1⟩ with
        | none => exact none
        | some shifted =>
            exact some
              { owner := shifted.owner
                refines := by
                  rw [shifted.initialBox]
                  exact grid.lowerRight_refines }
      else if upperRightWinding : (RFAP.Winding.quadrupledBoxWinding
          (rootPolynomial parameter) grid.upperRight = 4) then
        let candidate := grid.upperRight
        match directOwnerOnBox? parameter parameterNonzero candidate
            ⟨(midpoint_strict proper.1).2, (midpoint_strict proper.2).2⟩ with
        | none => exact none
        | some shifted =>
            exact some
              { owner := shifted.owner
                refines := by
                  rw [shifted.initialBox]
                  exact grid.upperRight_refines }
      else exact none
    else exact none
  else exact none

private def boxCenter (box : Box) : Gaussian :=
  ⟨midpoint box.xLower box.xUpper, midpoint box.yLower box.yUpper⟩

/-- Move three quarters of the way from a source coordinate toward a selected
midpoint-child centre.  Since a child centre is one quarter-width from its
parent centre, this moves the replacement window by three sixteenths of the
source width, the largest dyadic move used here while retaining a strict
overlap margin around that child. -/
private def gentleCoordinate (source target : Coordinate) : Coordinate :=
  midpoint target (midpoint source target)

private def gentleCenter (source child : Box) : Gaussian :=
  ⟨gentleCoordinate (boxCenter source).re (boxCenter child).re,
    gentleCoordinate (boxCenter source).im (boxCenter child).im⟩

/-- The executable, source-state-independent part of a moving reset.  Keeping
the selected candidate and its direct owner together lets explicit examples
evaluate the geometry from a cached box without reopening a transported
owner merely to rediscover that box. -/
private structure MovingCandidateData (parameter : Gaussian)
    (sourceBox child : Box) where
  candidate : Box
  childStrict : child.StrictInterior candidate
  moved : DirectBoxOwner parameter candidate

private def movingCandidateData? (parameter : Gaussian)
    (parameterNonzero : parameter ≠ 0) (sourceBox : Box)
    (sourceProper : sourceBox.Proper) (child : Box) :
    Option (MovingCandidateData parameter sourceBox child) := by
  let radius := sourceBox.widthX / 2
  have radiusPositive : 0 < radius := by
    exact RFAP.ConstructiveFraction.div_pos_direct
      (RFAP.ConstructiveFraction.sub_pos_direct sourceProper.1) (by decide)
  let candidate := RFAP.AffineWinding.centeredSquare
    (gentleCenter sourceBox child) radius radiusPositive.le
  if childStrict : child.StrictInterior candidate then
    match directOwnerOnBox? parameter parameterNonzero candidate
        (RFAP.AffineWinding.centeredSquare_proper
          (gentleCenter sourceBox child) radiusPositive) with
    | none => exact none
    | some moved => exact some ⟨candidate, childStrict, moved⟩
  else exact none

/-- A quadratic owner whose box may move instead of remaining nested.  The
displayed bridge owner refines the source and is strictly inside the moved
owner; refining that bridge once supplies the common strict tail used by the
operational-equivalence proof without making path evaluation run the generic
refiner eagerly. -/
structure MovingRecenter (parameter : Gaussian) (source : Owner parameter) where
  owner : Owner parameter
  /-- The directly certified box used to construct `owner`.  Retaining this
  value avoids transporting dependent boundary-clearance data merely to
  inspect its four executable side bounds. -/
  ownerBox : Box
  ownerInitialBox : owner.track.initial.box = ownerBox
  ownerAmbientBox : owner.ambient = ownerBox
  ownerDominance : AmbientClearanceDominance owner
  bridgeOwner : Owner parameter
  bridgeRefinesSource : bridgeOwner.track.initial.box.Refines
    source.track.initial.box
  bridgeStrictOwner : bridgeOwner.track.initial.box.StrictInterior
    owner.track.initial.box
  ownerLeftNonzero :
    CCL.Riemann.SquareRootContinuationChain.Owner.verticalDeterminant
      parameter ownerBox.xLower ≠ 0
  ownerRightNonzero :
    CCL.Riemann.SquareRootContinuationChain.Owner.verticalDeterminant
      parameter ownerBox.xUpper ≠ 0
  ownerBottomNonzero :
    CCL.Riemann.SquareRootContinuationChain.Owner.horizontalDeterminant
      parameter ownerBox.yLower ≠ 0
  ownerTopNonzero :
    CCL.Riemann.SquareRootContinuationChain.Owner.horizontalDeterminant
      parameter ownerBox.yUpper ≠ 0
  ownerDirectClearanceBound : owner.track.initial.clearance.bound =
    (directBoundaryClearance parameter ownerBox
      ownerLeftNonzero ownerRightNonzero ownerBottomNonzero
        ownerTopNonzero).bound
  ownerAmbientLeftClearanceBound :
    owner.track.initial.ambientLeftClearance.bound =
      (directBoundaryClearance parameter ownerBox
        ownerLeftNonzero ownerRightNonzero ownerBottomNonzero
          ownerTopNonzero).bound

private def movingCandidate? {parameter : Gaussian} (source : Owner parameter)
    (child : Box) (childRefines : child.Refines source.track.initial.box)
    (bridgeOwner : Owner parameter)
    (bridgeBox : bridgeOwner.track.initial.box = child) :
    Option (MovingRecenter parameter source) := by
  match movingCandidateData? parameter source.parameterNonzero
      source.track.initial.box source.track.initial.proper child with
    | none => exact none
    | some data =>
        exact some
          { owner := data.moved.owner
            ownerBox := data.candidate
            ownerInitialBox := data.moved.initialBox
            ownerAmbientBox := data.moved.ambientBox
            ownerDominance := data.moved.dominance
            bridgeOwner := bridgeOwner
            bridgeRefinesSource := by
              rw [bridgeBox]
              exact childRefines
            bridgeStrictOwner := by
              rw [bridgeBox, data.moved.initialBox]
              exact data.childStrict
            ownerLeftNonzero := data.moved.leftNonzero
            ownerRightNonzero := data.moved.rightNonzero
            ownerBottomNonzero := data.moved.bottomNonzero
            ownerTopNonzero := data.moved.topNonzero
            ownerDirectClearanceBound := data.moved.initialClearanceBound
            ownerAmbientLeftClearanceBound :=
              data.moved.ambientLeftClearanceBound }

/-- Move a quadratic continuation window gently toward an overlapping
midpoint child.  The replacement keeps the source width, is independently
checked for winding four, and carries a bridge that witnesses the same root. -/
def movingRecenter? {parameter : Gaussian} (source : Owner parameter) :
    Option (MovingRecenter parameter source) := by
  let box := source.track.initial.box
  let proper := source.track.initial.proper
  let xCut := midpoint box.xLower box.xUpper
  let yCut := midpoint box.yLower box.yUpper
  if xNonzero :
      CCL.Riemann.SquareRootContinuationChain.Owner.verticalDeterminant
        parameter xCut ≠ 0 then
    if yNonzero :
        CCL.Riemann.SquareRootContinuationChain.Owner.horizontalDeterminant
          parameter yCut ≠ 0 then
      let grid := midpointGrid parameter box proper xNonzero yNonzero
      if lowerLeftWinding : (RFAP.Winding.quadrupledBoxWinding
          (rootPolynomial parameter) grid.lowerLeft = 4) then
        let childClearances :=
          grid.childClearances source.track.initial.clearance
        let bridgeState := childState source grid.lowerLeft
          grid.lowerLeft_refines
          ⟨(midpoint_strict proper.1).1, (midpoint_strict proper.2).1⟩
          childClearances.1 lowerLeftWinding
          (RFAP.BoxClearance.leftOfBoundary source.track.initial.clearance)
          grid.verticalClearance
          (RFAP.BoxClearance.bottomOfBoundary source.track.initial.clearance)
          grid.horizontalClearance
        let bridgeOwner := ownerOfState source.parameterNonzero bridgeState
        exact movingCandidate? source grid.lowerLeft grid.lowerLeft_refines
          bridgeOwner rfl
      else if upperLeftWinding : (RFAP.Winding.quadrupledBoxWinding
          (rootPolynomial parameter) grid.upperLeft = 4) then
        let childClearances :=
          grid.childClearances source.track.initial.clearance
        let bridgeState := childState source grid.upperLeft
          grid.upperLeft_refines
          ⟨(midpoint_strict proper.1).1, (midpoint_strict proper.2).2⟩
          childClearances.2.1 upperLeftWinding
          (RFAP.BoxClearance.leftOfBoundary source.track.initial.clearance)
          grid.verticalClearance grid.horizontalClearance
          (RFAP.BoxClearance.topOfBoundary source.track.initial.clearance)
        let bridgeOwner := ownerOfState source.parameterNonzero bridgeState
        exact movingCandidate? source grid.upperLeft grid.upperLeft_refines
          bridgeOwner rfl
      else if lowerRightWinding : (RFAP.Winding.quadrupledBoxWinding
          (rootPolynomial parameter) grid.lowerRight = 4) then
        let childClearances :=
          grid.childClearances source.track.initial.clearance
        let bridgeState := childState source grid.lowerRight
          grid.lowerRight_refines
          ⟨(midpoint_strict proper.1).2, (midpoint_strict proper.2).1⟩
          childClearances.2.2.1 lowerRightWinding grid.verticalClearance
          (RFAP.BoxClearance.rightOfBoundary source.track.initial.clearance)
          (RFAP.BoxClearance.bottomOfBoundary source.track.initial.clearance)
          grid.horizontalClearance
        let bridgeOwner := ownerOfState source.parameterNonzero bridgeState
        exact movingCandidate? source grid.lowerRight grid.lowerRight_refines
          bridgeOwner rfl
      else if upperRightWinding : (RFAP.Winding.quadrupledBoxWinding
          (rootPolynomial parameter) grid.upperRight = 4) then
        let childClearances :=
          grid.childClearances source.track.initial.clearance
        let bridgeState := childState source grid.upperRight
          grid.upperRight_refines
          ⟨(midpoint_strict proper.1).2, (midpoint_strict proper.2).2⟩
          childClearances.2.2.2 upperRightWinding grid.verticalClearance
          (RFAP.BoxClearance.rightOfBoundary source.track.initial.clearance)
          grid.horizontalClearance
          (RFAP.BoxClearance.topOfBoundary source.track.initial.clearance)
        let bridgeOwner := ownerOfState source.parameterNonzero bridgeState
        exact movingCandidate? source grid.upperRight grid.upperRight_refines
          bridgeOwner rfl
      else exact none
    else exact none
  else exact none

/-- Box-only projection of `movingRecenter?`.  Its branch decisions and
candidate checks are identical, but it consumes an already cached source box
and properness proof instead of reducing an entire transported owner. -/
def movingRecenterBox? (parameter : Gaussian) (parameterNonzero : parameter ≠ 0)
    (box : Box) (proper : box.Proper) : Option Box := by
  let xCut := midpoint box.xLower box.xUpper
  let yCut := midpoint box.yLower box.yUpper
  if xNonzero :
      CCL.Riemann.SquareRootContinuationChain.Owner.verticalDeterminant
        parameter xCut ≠ 0 then
    if yNonzero :
        CCL.Riemann.SquareRootContinuationChain.Owner.horizontalDeterminant
          parameter yCut ≠ 0 then
      let grid := midpointGrid parameter box proper xNonzero yNonzero
      if lowerLeftWinding : (RFAP.Winding.quadrupledBoxWinding
          (rootPolynomial parameter) grid.lowerLeft = 4) then
        exact Option.map MovingCandidateData.candidate
          (movingCandidateData? parameter parameterNonzero box proper
            grid.lowerLeft)
      else if upperLeftWinding : (RFAP.Winding.quadrupledBoxWinding
          (rootPolynomial parameter) grid.upperLeft = 4) then
        exact Option.map MovingCandidateData.candidate
          (movingCandidateData? parameter parameterNonzero box proper
            grid.upperLeft)
      else if lowerRightWinding : (RFAP.Winding.quadrupledBoxWinding
          (rootPolynomial parameter) grid.lowerRight = 4) then
        exact Option.map MovingCandidateData.candidate
          (movingCandidateData? parameter parameterNonzero box proper
            grid.lowerRight)
      else if upperRightWinding : (RFAP.Winding.quadrupledBoxWinding
          (rootPolynomial parameter) grid.upperRight = 4) then
        exact Option.map MovingCandidateData.candidate
          (movingCandidateData? parameter parameterNonzero box proper
            grid.upperRight)
      else exact none
    else exact none
  else exact none

private theorem movingCandidate_ownerBox_map {parameter : Gaussian}
    (source : Owner parameter) (child : Box)
    (childRefines : child.Refines source.track.initial.box)
    (bridgeOwner : Owner parameter)
    (bridgeBox : bridgeOwner.track.initial.box = child) :
    Option.map (fun reset => reset.ownerBox)
        (movingCandidate? source child childRefines bridgeOwner bridgeBox) =
      Option.map MovingCandidateData.candidate
        (movingCandidateData? parameter source.parameterNonzero
          source.track.initial.box source.track.initial.proper child) := by
  unfold movingCandidate?
  generalize found : movingCandidateData? parameter source.parameterNonzero
    source.track.initial.box source.track.initial.proper child = result
  cases result <;> rfl

/-- The full reset and its box-only cached projection make exactly the same
finite branch choices. -/
theorem movingRecenter_ownerBox_map {parameter : Gaussian}
    (source : Owner parameter) :
    Option.map (fun reset => reset.ownerBox) (movingRecenter? source) =
      movingRecenterBox? parameter source.parameterNonzero
        source.track.initial.box source.track.initial.proper := by
  unfold movingRecenter? movingRecenterBox?
  dsimp only
  split
  · split
    · split
      · exact movingCandidate_ownerBox_map _ _ _ _ _
      · split
        · exact movingCandidate_ownerBox_map _ _ _ _ _
        · split
          · exact movingCandidate_ownerBox_map _ _ _ _ _
          · split
            · exact movingCandidate_ownerBox_map _ _ _ _ _
            · rfl
    · rfl
  · rfl

/-- Replace the source box in the cached projection by any propositionally
equal stored box.  The properness witness is proof-only. -/
theorem movingRecenter_ownerBox_map_of_box {parameter : Gaussian}
    (source : Owner parameter) (box : Box) (proper : box.Proper)
    (boxEq : source.track.initial.box = box) :
    Option.map (fun reset => reset.ownerBox) (movingRecenter? source) =
      movingRecenterBox? parameter source.parameterNonzero box proper := by
  subst box
  exact movingRecenter_ownerBox_map source

/-- The original resultant-based same-box transport, retained as the total
fallback when the cheaper transported ambient clearances do not all carry the
requested move. -/
private def resultantReservedTransport {source target : Gaussian}
    (owner : Owner source) (targetNonzero : target ≠ 0)
    (small : RFAP.ConstructiveGaussian.Gaussian.normSq (source - target) <
      owner.track.initial.clearance.bound) (reserve : Coordinate) :
    Owner target :=
  let box := owner.track.initial.box
  let carried := CCL.Riemann.SquareRootContinuation.transportedOwner
    owner.track.initial small
  if leftNonzero :
      CCL.Riemann.SquareRootContinuationChain.Owner.verticalDeterminant
        target box.xLower ≠ 0 then
    if rightNonzero :
        CCL.Riemann.SquareRootContinuationChain.Owner.verticalDeterminant
          target box.xUpper ≠ 0 then
      if bottomNonzero :
          CCL.Riemann.SquareRootContinuationChain.Owner.horizontalDeterminant
            target box.yLower ≠ 0 then
        if topNonzero :
            CCL.Riemann.SquareRootContinuationChain.Owner.horizontalDeterminant
              target box.yUpper ≠ 0 then
          if _reserveSmall : reserve <
              (directBoundaryClearance target box leftNonzero rightNonzero
                bottomNonzero topNonzero).bound then
            directOwnerOfBox target targetNonzero box carried.proper leftNonzero
              rightNonzero bottomNonzero topNonzero carried.rawWindingFour
          else
            match midpointRecenter? target targetNonzero box carried.proper
                with
            | some recentered => recentered.owner
            | none => owner.advance targetNonzero small
        else owner.advance targetNonzero small
      else owner.advance targetNonzero small
    else owner.advance targetNonzero small
  else owner.advance targetNonzero small

/-- Reserved transport stays on the source box or uses a strict generic
descendant, so its initial box always refines the source box. -/
private theorem resultantReservedTransport_initial_box_refines
    {source target : Gaussian}
    (owner : Owner source) (targetNonzero : target ≠ 0)
    (small : RFAP.ConstructiveGaussian.Gaussian.normSq (source - target) <
      owner.track.initial.clearance.bound) (reserve : Coordinate) :
    (resultantReservedTransport owner targetNonzero small reserve).track.initial.box.Refines
      owner.track.initial.box := by
  unfold resultantReservedTransport
  dsimp only
  by_cases leftNonzero :
      CCL.Riemann.SquareRootContinuationChain.Owner.verticalDeterminant
        target owner.track.initial.box.xLower ≠ 0
  · rw [dif_pos leftNonzero]
    by_cases rightNonzero :
        CCL.Riemann.SquareRootContinuationChain.Owner.verticalDeterminant
          target owner.track.initial.box.xUpper ≠ 0
    · rw [dif_pos rightNonzero]
      by_cases bottomNonzero :
          CCL.Riemann.SquareRootContinuationChain.Owner.horizontalDeterminant
            target owner.track.initial.box.yLower ≠ 0
      · rw [dif_pos bottomNonzero]
        by_cases topNonzero :
            CCL.Riemann.SquareRootContinuationChain.Owner.horizontalDeterminant
              target owner.track.initial.box.yUpper ≠ 0
        · rw [dif_pos topNonzero]
          by_cases reserveSmall : reserve <
              (directBoundaryClearance target owner.track.initial.box
                leftNonzero rightNonzero bottomNonzero topNonzero).bound
          · rw [dif_pos reserveSmall, directOwnerOfBox_initial_box]
            exact RFAP.Boxes.Box.refines_refl _
          · rw [dif_neg reserveSmall]
            generalize recenteredEq : midpointRecenter? target targetNonzero
              owner.track.initial.box
              (CCL.Riemann.SquareRootContinuation.transportedOwner
                owner.track.initial small).proper = recentered
            cases recentered with
            | none =>
                change (owner.advance targetNonzero small).track.initial.box.Refines
                  owner.track.initial.box
                exact owner.advance_initial_box_refines targetNonzero small
            | some centered =>
                simp only
                exact centered.refines
        · rw [dif_neg topNonzero]
          exact owner.advance_initial_box_refines targetNonzero small
      · rw [dif_neg bottomNonzero]
        exact owner.advance_initial_box_refines targetNonzero small
    · rw [dif_neg rightNonzero]
      exact owner.advance_initial_box_refines targetNonzero small
  · rw [dif_neg leftNonzero]
    exact owner.advance_initial_box_refines targetNonzero small

/-- Structural data showing that a direct or recentered result remains in a
same-occurrence target owner on the transported parent box. -/
structure DirectPresentationRelation {source target : Gaussian}
    (owner : Owner source) (targetNonzero : target ≠ 0)
    (small : RFAP.ConstructiveGaussian.Gaussian.normSq (source - target) <
      owner.track.initial.clearance.bound)
    (result : Owner target) where
  parent : Owner target
  genericStrictParent :
    (owner.advance targetNonzero small).track.initial.box.StrictInterior
      parent.track.initial.box
  resultRefinesParent : result.track.initial.box.Refines parent.track.initial.box

/-- Computational branch data for reserved transport. -/
private def resultantReservedTransport_generic_relation
    {source target : Gaussian}
    (owner : Owner source) (targetNonzero : target ≠ 0)
    (small : RFAP.ConstructiveGaussian.Gaussian.normSq (source - target) <
      owner.track.initial.clearance.bound) (reserve : Coordinate) :
    PSum
      (resultantReservedTransport owner targetNonzero small reserve =
        owner.advance targetNonzero small)
      (DirectPresentationRelation owner targetNonzero small
        (resultantReservedTransport owner targetNonzero small reserve)) := by
  unfold resultantReservedTransport
  dsimp only
  by_cases leftNonzero :
      CCL.Riemann.SquareRootContinuationChain.Owner.verticalDeterminant
        target owner.track.initial.box.xLower ≠ 0
  · rw [dif_pos leftNonzero]
    by_cases rightNonzero :
        CCL.Riemann.SquareRootContinuationChain.Owner.verticalDeterminant
          target owner.track.initial.box.xUpper ≠ 0
    · rw [dif_pos rightNonzero]
      by_cases bottomNonzero :
          CCL.Riemann.SquareRootContinuationChain.Owner.horizontalDeterminant
            target owner.track.initial.box.yLower ≠ 0
      · rw [dif_pos bottomNonzero]
        by_cases topNonzero :
            CCL.Riemann.SquareRootContinuationChain.Owner.horizontalDeterminant
              target owner.track.initial.box.yUpper ≠ 0
        · rw [dif_pos topNonzero]
          by_cases reserveSmall : reserve <
              (directBoundaryClearance target owner.track.initial.box
                leftNonzero rightNonzero bottomNonzero topNonzero).bound
          · rw [dif_pos reserveSmall]
            exact PSum.inr
              { parent := directOwnerOfBox target targetNonzero
                  owner.track.initial.box
                  (CCL.Riemann.SquareRootContinuation.transportedOwner
                    owner.track.initial small).proper
                  leftNonzero rightNonzero bottomNonzero topNonzero
                  (CCL.Riemann.SquareRootContinuation.transportedOwner
                    owner.track.initial small).rawWindingFour
                genericStrictParent := by
                  change (owner.advance targetNonzero small).track.initial.box
                    |>.StrictInterior owner.track.initial.box
                  exact CCL.Riemann.SquareRootContinuation.continuedTrack_initial_strict_source
                    targetNonzero owner.track.initial small
                resultRefinesParent := by
                  change owner.track.initial.box.Refines owner.track.initial.box
                  exact RFAP.Boxes.Box.refines_refl _ }
          · rw [dif_neg reserveSmall]
            generalize recenteredEq : midpointRecenter? target targetNonzero
              owner.track.initial.box
              (CCL.Riemann.SquareRootContinuation.transportedOwner
                owner.track.initial small).proper = recentered
            cases recentered with
            | none =>
                change PSum
                  (owner.advance targetNonzero small =
                    owner.advance targetNonzero small)
                  (DirectPresentationRelation owner targetNonzero small
                    (owner.advance targetNonzero small))
                exact PSum.inl rfl
            | some centered =>
                simp only
                exact PSum.inr
                  { parent := directOwnerOfBox target targetNonzero
                      owner.track.initial.box
                      (CCL.Riemann.SquareRootContinuation.transportedOwner
                        owner.track.initial small).proper
                      leftNonzero rightNonzero bottomNonzero topNonzero
                      (CCL.Riemann.SquareRootContinuation.transportedOwner
                        owner.track.initial small).rawWindingFour
                    genericStrictParent := by
                      change
                        (owner.advance targetNonzero small).track.initial.box
                          |>.StrictInterior owner.track.initial.box
                      exact CCL.Riemann.SquareRootContinuation.continuedTrack_initial_strict_source
                        targetNonzero owner.track.initial small
                    resultRefinesParent := centered.refines }
        · rw [dif_neg topNonzero]
          exact PSum.inl rfl
      · rw [dif_neg bottomNonzero]
        exact PSum.inl rfl
    · rw [dif_neg rightNonzero]
      exact PSum.inl rfl
  · rw [dif_neg leftNonzero]
    exact PSum.inl rfl

/-- Transport the source owner's left ambient-line clearance to a target
quadratic parameter. -/
def ambientLeftAfterMove {source target : Gaussian}
    (owner : Owner source)
    (leftSmall : RFAP.ConstructiveGaussian.Gaussian.normSq (source - target) <
      owner.track.initial.ambientLeftClearance.bound) :=
  CCL.PowerMonodromy.verticalClearanceAfterMove
    (target := target) CCL.Riemann.SquareRootSheets.degreeTwo
      owner.track.initial.ambientLeftClearance leftSmall

/-- A transported left-side clearance is bounded by one quarter of the
square of its source bound.  This inexpensive upper estimate is useful to
cache branch decisions after a successful ambient Rouché transport. -/
theorem ambientLeftAfterMove_bound_le_quarter_sq
    {source target : Gaussian} (owner : Owner source)
    (leftSmall : RFAP.ConstructiveGaussian.Gaussian.normSq (source - target) <
      owner.track.initial.ambientLeftClearance.bound) :
    (ambientLeftAfterMove owner leftSmall).bound ≤
      owner.track.initial.ambientLeftClearance.bound ^ 2 / 4 := by
  rw [ambientLeftAfterMove,
    CCL.PowerMonodromy.verticalClearanceAfterMove_bound]
  let displacement :=
    RFAP.ConstructiveGaussian.Gaussian.normSq (source - target)
  let clearance := owner.track.initial.ambientLeftClearance.bound
  let majorant := max 1
    (RFAP.PathClearance.evalSqBound
        (RFAP.PathPolynomial.pathReal
          (CCL.PowerMonodromy.polynomial source
            CCL.Riemann.SquareRootSheets.degreeTwo)
          (RFAP.Winding.verticalBase owner.track.initial.box.xLower)
          RFAP.Winding.verticalDirection)
        (RFAP.BoxClearance.verticalInterval owner.ambient) +
      RFAP.PathClearance.evalSqBound
        (RFAP.PathPolynomial.pathImag
          (CCL.PowerMonodromy.polynomial source
            CCL.Riemann.SquareRootSheets.degreeTwo)
          (RFAP.Winding.verticalBase owner.track.initial.box.xLower)
          RFAP.Winding.verticalDirection)
        (RFAP.BoxClearance.verticalInterval owner.ambient))
  have displacementNonnegative : 0 ≤ displacement :=
    RFAP.ConstructiveGaussian.Gaussian.normSq_nonneg _
  have marginNonnegative : 0 ≤ clearance - displacement :=
    RFAP.ConstructiveFraction.sub_nonneg_direct leftSmall.le
  have marginLe : clearance - displacement ≤ clearance := by
    calc
      clearance - displacement ≤ clearance - 0 :=
        RFAP.ConstructiveFraction.sub_le_sub_left_direct
          displacementNonnegative clearance
      _ = clearance := by ring1
  have squareLe : (clearance - displacement) ^ 2 ≤ clearance ^ 2 :=
    RFAP.ConstructiveFraction.pow_le_pow_direct marginNonnegative marginLe 2
  have denominatorLe : (4 : Coordinate) ≤ 4 * majorant := by
    calc
      (4 : Coordinate) = 4 * 1 := by ring1
      _ ≤ 4 * majorant :=
        RFAP.ConstructiveFraction.mul_le_mul_of_nonneg_left_direct
          (le_max_left _ _) (by decide)
  calc
    (clearance - displacement) ^ 2 / (4 * majorant) ≤
        (clearance - displacement) ^ 2 / 4 :=
      RFAP.ConstructiveFraction.div_le_div_of_nonneg_left_direct
        (RFAP.ConstructiveFraction.sq_nonneg_direct
          (clearance - displacement)) (by decide) denominatorLe
    _ ≤ clearance ^ 2 / 4 := by
      change (clearance - displacement) ^ 2 * (4 : Coordinate)⁻¹ ≤
        clearance ^ 2 * (4 : Coordinate)⁻¹
      exact RFAP.ConstructiveFraction.mul_le_mul_of_nonneg_right_direct
        squareLe
        (RFAP.ConstructiveFraction.inv_pos_direct (by decide)).le

/-- Transport the source owner's right ambient-line clearance. -/
def ambientRightAfterMove {source target : Gaussian}
    (owner : Owner source)
    (rightSmall : RFAP.ConstructiveGaussian.Gaussian.normSq (source - target) <
      owner.track.initial.ambientRightClearance.bound) :=
  CCL.PowerMonodromy.verticalClearanceAfterMove
    (target := target) CCL.Riemann.SquareRootSheets.degreeTwo
      owner.track.initial.ambientRightClearance rightSmall

/-- Transport the source owner's bottom ambient-line clearance. -/
def ambientBottomAfterMove {source target : Gaussian}
    (owner : Owner source)
    (bottomSmall : RFAP.ConstructiveGaussian.Gaussian.normSq (source - target) <
      owner.track.initial.ambientBottomClearance.bound) :=
  CCL.PowerMonodromy.horizontalClearanceAfterMove
    (target := target) CCL.Riemann.SquareRootSheets.degreeTwo
      owner.track.initial.ambientBottomClearance bottomSmall

/-- Transport the source owner's top ambient-line clearance. -/
def ambientTopAfterMove {source target : Gaussian}
    (owner : Owner source)
    (topSmall : RFAP.ConstructiveGaussian.Gaussian.normSq (source - target) <
      owner.track.initial.ambientTopClearance.bound) :=
  CCL.PowerMonodromy.horizontalClearanceAfterMove
    (target := target) CCL.Riemann.SquareRootSheets.degreeTwo
      owner.track.initial.ambientTopClearance topSmall

/-- Assemble the transported boundary clearance from the four transported
ambient-line certificates restricted to the displayed owner box. -/
def ambientAfterMoveClearance {source target : Gaussian}
    (owner : Owner source)
    (leftSmall : RFAP.ConstructiveGaussian.Gaussian.normSq (source - target) <
      owner.track.initial.ambientLeftClearance.bound)
    (rightSmall : RFAP.ConstructiveGaussian.Gaussian.normSq (source - target) <
      owner.track.initial.ambientRightClearance.bound)
    (bottomSmall : RFAP.ConstructiveGaussian.Gaussian.normSq (source - target) <
      owner.track.initial.ambientBottomClearance.bound)
    (topSmall : RFAP.ConstructiveGaussian.Gaussian.normSq (source - target) <
      owner.track.initial.ambientTopClearance.bound) :
    RFAP.BoxClearance.BoundaryClearance (rootPolynomial target)
      owner.track.initial.box :=
  RFAP.BoxClearance.boundaryOfLines
    ((ambientLeftAfterMove owner leftSmall).restrict
      owner.track.initial.refinesAmbient)
    ((ambientRightAfterMove owner rightSmall).restrict
      owner.track.initial.refinesAmbient)
    ((ambientBottomAfterMove owner bottomSmall).restrict
      owner.track.initial.refinesAmbient)
    ((ambientTopAfterMove owner topSmall).restrict
      owner.track.initial.refinesAmbient)

/-- The cached rational calculation underlying ambient Rouché transport. -/
@[simp] theorem ambientAfterMoveClearance_bound {source target : Gaussian}
    (owner : Owner source)
    (leftSmall : RFAP.ConstructiveGaussian.Gaussian.normSq (source - target) <
      owner.track.initial.ambientLeftClearance.bound)
    (rightSmall : RFAP.ConstructiveGaussian.Gaussian.normSq (source - target) <
      owner.track.initial.ambientRightClearance.bound)
    (bottomSmall : RFAP.ConstructiveGaussian.Gaussian.normSq (source - target) <
      owner.track.initial.ambientBottomClearance.bound)
    (topSmall : RFAP.ConstructiveGaussian.Gaussian.normSq (source - target) <
      owner.track.initial.ambientTopClearance.bound) :
    (ambientAfterMoveClearance owner leftSmall rightSmall bottomSmall
        topSmall).bound =
      min (ambientLeftAfterMove owner leftSmall).bound
        (min (ambientRightAfterMove owner rightSmall).bound
          (min (ambientBottomAfterMove owner bottomSmall).bound
            (ambientTopAfterMove owner topSmall).bound)) := by
  unfold ambientAfterMoveClearance
  rw [RFAP.BoxClearance.boundaryOfLines_bound,
    RFAP.BoxClearance.VerticalLineClearance.restrict_bound,
    RFAP.BoxClearance.VerticalLineClearance.restrict_bound,
    RFAP.BoxClearance.HorizontalLineClearance.restrict_bound,
    RFAP.BoxClearance.HorizontalLineClearance.restrict_bound]

/-- The transported initial state, with its boundary clearance assembled from
the same four ambient-line transports retained in the state. -/
private def ambientRoucheState {source target : Gaussian}
    (owner : Owner source) (_targetNonzero : target ≠ 0)
    (small : RFAP.ConstructiveGaussian.Gaussian.normSq (source - target) <
      owner.track.initial.clearance.bound)
    (leftSmall : RFAP.ConstructiveGaussian.Gaussian.normSq (source - target) <
      owner.track.initial.ambientLeftClearance.bound)
    (rightSmall : RFAP.ConstructiveGaussian.Gaussian.normSq (source - target) <
      owner.track.initial.ambientRightClearance.bound)
    (bottomSmall : RFAP.ConstructiveGaussian.Gaussian.normSq (source - target) <
      owner.track.initial.ambientBottomClearance.bound)
    (topSmall : RFAP.ConstructiveGaussian.Gaussian.normSq (source - target) <
      owner.track.initial.ambientTopClearance.bound) :
    RFAP.ShrinkingTrack.WindingOneState (rootPolynomial target) owner.ambient := by
  let carried := CCL.Riemann.SquareRootContinuation.transportedOwner
    owner.track.initial small
  exact
    { box := owner.track.initial.box
      refinesAmbient := owner.track.initial.refinesAmbient
      proper := carried.proper
      clearance := ambientAfterMoveClearance owner leftSmall rightSmall
        bottomSmall topSmall
      rawWindingFour := carried.rawWindingFour
      ambientLeftClearance := ambientLeftAfterMove owner leftSmall
      ambientRightClearance := ambientRightAfterMove owner rightSmall
      ambientBottomClearance := ambientBottomAfterMove owner bottomSmall
      ambientTopClearance := ambientTopAfterMove owner topSmall }

/-- Carry the complete source state by the already available constant-term
Rouché estimates.  Unlike the resultant fallback, this only subtracts the
displayed squared displacement from five rational clearance bounds. -/
private def ambientRoucheTransport {source target : Gaussian}
    (owner : Owner source) (targetNonzero : target ≠ 0)
    (small : RFAP.ConstructiveGaussian.Gaussian.normSq (source - target) <
      owner.track.initial.clearance.bound)
    (leftSmall : RFAP.ConstructiveGaussian.Gaussian.normSq (source - target) <
      owner.track.initial.ambientLeftClearance.bound)
    (rightSmall : RFAP.ConstructiveGaussian.Gaussian.normSq (source - target) <
      owner.track.initial.ambientRightClearance.bound)
    (bottomSmall : RFAP.ConstructiveGaussian.Gaussian.normSq (source - target) <
      owner.track.initial.ambientBottomClearance.bound)
    (topSmall : RFAP.ConstructiveGaussian.Gaussian.normSq (source - target) <
      owner.track.initial.ambientTopClearance.bound) : Owner target :=
  ownerOfState targetNonzero
    (ambientRoucheState owner targetNonzero small leftSmall rightSmall
      bottomSmall topSmall)

private theorem ambientRoucheTransport_initial_box {source target : Gaussian}
    (owner : Owner source) (targetNonzero : target ≠ 0)
    (small : RFAP.ConstructiveGaussian.Gaussian.normSq (source - target) <
      owner.track.initial.clearance.bound)
    (leftSmall : RFAP.ConstructiveGaussian.Gaussian.normSq (source - target) <
      owner.track.initial.ambientLeftClearance.bound)
    (rightSmall : RFAP.ConstructiveGaussian.Gaussian.normSq (source - target) <
      owner.track.initial.ambientRightClearance.bound)
    (bottomSmall : RFAP.ConstructiveGaussian.Gaussian.normSq (source - target) <
      owner.track.initial.ambientBottomClearance.bound)
    (topSmall : RFAP.ConstructiveGaussian.Gaussian.normSq (source - target) <
      owner.track.initial.ambientTopClearance.bound) :
    (ambientRoucheTransport owner targetNonzero small leftSmall rightSmall
      bottomSmall topSmall).track.initial.box = owner.track.initial.box := rfl

private theorem ambientRoucheTransport_ambient {source target : Gaussian}
    (owner : Owner source) (targetNonzero : target ≠ 0)
    (small : RFAP.ConstructiveGaussian.Gaussian.normSq (source - target) <
      owner.track.initial.clearance.bound)
    (leftSmall : RFAP.ConstructiveGaussian.Gaussian.normSq (source - target) <
      owner.track.initial.ambientLeftClearance.bound)
    (rightSmall : RFAP.ConstructiveGaussian.Gaussian.normSq (source - target) <
      owner.track.initial.ambientRightClearance.bound)
    (bottomSmall : RFAP.ConstructiveGaussian.Gaussian.normSq (source - target) <
      owner.track.initial.ambientBottomClearance.bound)
    (topSmall : RFAP.ConstructiveGaussian.Gaussian.normSq (source - target) <
      owner.track.initial.ambientTopClearance.bound) :
    (ambientRoucheTransport owner targetNonzero small leftSmall rightSmall
      bottomSmall topSmall).ambient = owner.ambient := rfl

private theorem ambientAfterMoveClearance_le_left
    {source target : Gaussian} (owner : Owner source)
    (leftSmall : RFAP.ConstructiveGaussian.Gaussian.normSq (source - target) <
      owner.track.initial.ambientLeftClearance.bound)
    (rightSmall : RFAP.ConstructiveGaussian.Gaussian.normSq (source - target) <
      owner.track.initial.ambientRightClearance.bound)
    (bottomSmall : RFAP.ConstructiveGaussian.Gaussian.normSq (source - target) <
      owner.track.initial.ambientBottomClearance.bound)
    (topSmall : RFAP.ConstructiveGaussian.Gaussian.normSq (source - target) <
      owner.track.initial.ambientTopClearance.bound) :
    (ambientAfterMoveClearance owner leftSmall rightSmall bottomSmall
      topSmall).bound <= (ambientLeftAfterMove owner leftSmall).bound := by
  let left := ambientLeftAfterMove owner leftSmall
  let right := ambientRightAfterMove owner rightSmall
  let bottom := ambientBottomAfterMove owner bottomSmall
  let top := ambientTopAfterMove owner topSmall
  let refines := owner.track.initial.refinesAmbient
  calc
    (ambientAfterMoveClearance owner leftSmall rightSmall bottomSmall
        topSmall).bound =
        (RFAP.BoxClearance.boundaryOfLines (left.restrict refines)
          (right.restrict refines) (bottom.restrict refines)
          (top.restrict refines)).bound := rfl
    _ <= (left.restrict refines).bound :=
      RFAP.BoxClearance.boundaryOfLines_bound_le_left _ _ _ _
    _ = left.bound := RFAP.BoxClearance.VerticalLineClearance.restrict_bound _ _

private theorem ambientAfterMoveClearance_le_right
    {source target : Gaussian} (owner : Owner source)
    (leftSmall : RFAP.ConstructiveGaussian.Gaussian.normSq (source - target) <
      owner.track.initial.ambientLeftClearance.bound)
    (rightSmall : RFAP.ConstructiveGaussian.Gaussian.normSq (source - target) <
      owner.track.initial.ambientRightClearance.bound)
    (bottomSmall : RFAP.ConstructiveGaussian.Gaussian.normSq (source - target) <
      owner.track.initial.ambientBottomClearance.bound)
    (topSmall : RFAP.ConstructiveGaussian.Gaussian.normSq (source - target) <
      owner.track.initial.ambientTopClearance.bound) :
    (ambientAfterMoveClearance owner leftSmall rightSmall bottomSmall
      topSmall).bound <= (ambientRightAfterMove owner rightSmall).bound := by
  let left := ambientLeftAfterMove owner leftSmall
  let right := ambientRightAfterMove owner rightSmall
  let bottom := ambientBottomAfterMove owner bottomSmall
  let top := ambientTopAfterMove owner topSmall
  let refines := owner.track.initial.refinesAmbient
  calc
    (ambientAfterMoveClearance owner leftSmall rightSmall bottomSmall
        topSmall).bound =
        (RFAP.BoxClearance.boundaryOfLines (left.restrict refines)
          (right.restrict refines) (bottom.restrict refines)
          (top.restrict refines)).bound := rfl
    _ <= (right.restrict refines).bound :=
      RFAP.BoxClearance.boundaryOfLines_bound_le_right _ _ _ _
    _ = right.bound := RFAP.BoxClearance.VerticalLineClearance.restrict_bound _ _

private theorem ambientAfterMoveClearance_le_bottom
    {source target : Gaussian} (owner : Owner source)
    (leftSmall : RFAP.ConstructiveGaussian.Gaussian.normSq (source - target) <
      owner.track.initial.ambientLeftClearance.bound)
    (rightSmall : RFAP.ConstructiveGaussian.Gaussian.normSq (source - target) <
      owner.track.initial.ambientRightClearance.bound)
    (bottomSmall : RFAP.ConstructiveGaussian.Gaussian.normSq (source - target) <
      owner.track.initial.ambientBottomClearance.bound)
    (topSmall : RFAP.ConstructiveGaussian.Gaussian.normSq (source - target) <
      owner.track.initial.ambientTopClearance.bound) :
    (ambientAfterMoveClearance owner leftSmall rightSmall bottomSmall
      topSmall).bound <= (ambientBottomAfterMove owner bottomSmall).bound := by
  let left := ambientLeftAfterMove owner leftSmall
  let right := ambientRightAfterMove owner rightSmall
  let bottom := ambientBottomAfterMove owner bottomSmall
  let top := ambientTopAfterMove owner topSmall
  let refines := owner.track.initial.refinesAmbient
  calc
    (ambientAfterMoveClearance owner leftSmall rightSmall bottomSmall
        topSmall).bound =
        (RFAP.BoxClearance.boundaryOfLines (left.restrict refines)
          (right.restrict refines) (bottom.restrict refines)
          (top.restrict refines)).bound := rfl
    _ <= (bottom.restrict refines).bound :=
      RFAP.BoxClearance.boundaryOfLines_bound_le_bottom _ _ _ _
    _ = bottom.bound :=
      RFAP.BoxClearance.HorizontalLineClearance.restrict_bound _ _

private theorem ambientAfterMoveClearance_le_top
    {source target : Gaussian} (owner : Owner source)
    (leftSmall : RFAP.ConstructiveGaussian.Gaussian.normSq (source - target) <
      owner.track.initial.ambientLeftClearance.bound)
    (rightSmall : RFAP.ConstructiveGaussian.Gaussian.normSq (source - target) <
      owner.track.initial.ambientRightClearance.bound)
    (bottomSmall : RFAP.ConstructiveGaussian.Gaussian.normSq (source - target) <
      owner.track.initial.ambientBottomClearance.bound)
    (topSmall : RFAP.ConstructiveGaussian.Gaussian.normSq (source - target) <
      owner.track.initial.ambientTopClearance.bound) :
    (ambientAfterMoveClearance owner leftSmall rightSmall bottomSmall
      topSmall).bound <= (ambientTopAfterMove owner topSmall).bound := by
  let left := ambientLeftAfterMove owner leftSmall
  let right := ambientRightAfterMove owner rightSmall
  let bottom := ambientBottomAfterMove owner bottomSmall
  let top := ambientTopAfterMove owner topSmall
  let refines := owner.track.initial.refinesAmbient
  calc
    (ambientAfterMoveClearance owner leftSmall rightSmall bottomSmall
        topSmall).bound =
        (RFAP.BoxClearance.boundaryOfLines (left.restrict refines)
          (right.restrict refines) (bottom.restrict refines)
          (top.restrict refines)).bound := rfl
    _ <= (top.restrict refines).bound :=
      RFAP.BoxClearance.boundaryOfLines_bound_le_top _ _ _ _
    _ = top.bound :=
      RFAP.BoxClearance.HorizontalLineClearance.restrict_bound _ _

/-- Same-box Rouché transport with a requested target-clearance reserve.
The inexpensive transported-clearance branch is tried first; exact
resultants and finite Newton recentering remain a total fallback. -/
def reservedTransport {source target : Gaussian}
    (owner : Owner source) (targetNonzero : target ≠ 0)
    (small : RFAP.ConstructiveGaussian.Gaussian.normSq (source - target) <
      owner.track.initial.clearance.bound) (reserve : Coordinate) :
    Owner target :=
  if same : source = target then
    same ▸ owner
  else
    let displacement :=
      RFAP.ConstructiveGaussian.Gaussian.normSq (source - target)
    if leftSmall : displacement <
        owner.track.initial.ambientLeftClearance.bound then
      if rightSmall : displacement <
          owner.track.initial.ambientRightClearance.bound then
        if bottomSmall : displacement <
            owner.track.initial.ambientBottomClearance.bound then
          if topSmall : displacement <
              owner.track.initial.ambientTopClearance.bound then
            let carried := CCL.Riemann.SquareRootContinuation.transportedOwner
              owner.track.initial small
            if _reserveSmall : reserve < carried.clearance.bound then
              ambientRoucheTransport owner targetNonzero small leftSmall
                rightSmall bottomSmall topSmall
            else
              resultantReservedTransport owner targetNonzero small reserve
          else resultantReservedTransport owner targetNonzero small reserve
        else resultantReservedTransport owner targetNonzero small reserve
      else resultantReservedTransport owner targetNonzero small reserve
    else resultantReservedTransport owner targetNonzero small reserve

/-- Equal source owners give equal reserved transports, independently of the
proof witnesses carried by the two calls. -/
theorem reservedTransport_congr_owner
    {source target : Gaussian} {left right : Owner source}
    (same : left = right)
    (leftTargetNonzero rightTargetNonzero : target ≠ 0)
    (leftSmall : RFAP.ConstructiveGaussian.Gaussian.normSq (source - target) <
      left.track.initial.clearance.bound)
    (rightSmall : RFAP.ConstructiveGaussian.Gaussian.normSq (source - target) <
      right.track.initial.clearance.bound)
    (reserve : Coordinate) :
    reservedTransport left leftTargetNonzero leftSmall reserve =
      reservedTransport right rightTargetNonzero rightSmall reserve := by
  subst right
  rfl

/-- Public structural cache for the inexpensive ambient-Rouché branch of
`reservedTransport`.  Downstream continuation proofs can use the retained box
and the fact that its boundary clearance controls every ambient line without
reopening the nested branch search. -/
structure AmbientReservedTransportCache {source target : Gaussian}
    (owner : Owner source) (targetNonzero : target ≠ 0)
    (small : RFAP.ConstructiveGaussian.Gaussian.normSq (source - target) <
      owner.track.initial.clearance.bound) (reserve : Coordinate)
    (leftSmall : RFAP.ConstructiveGaussian.Gaussian.normSq (source - target) <
      owner.track.initial.ambientLeftClearance.bound)
    (rightSmall : RFAP.ConstructiveGaussian.Gaussian.normSq (source - target) <
      owner.track.initial.ambientRightClearance.bound)
    (bottomSmall : RFAP.ConstructiveGaussian.Gaussian.normSq (source - target) <
      owner.track.initial.ambientBottomClearance.bound)
    (topSmall : RFAP.ConstructiveGaussian.Gaussian.normSq (source - target) <
      owner.track.initial.ambientTopClearance.bound) where
  initialBox :
    (reservedTransport owner targetNonzero small reserve).track.initial.box =
      owner.track.initial.box
  ambientBox :
    (reservedTransport owner targetNonzero small reserve).ambient = owner.ambient
  ambientLeftBound :
    (reservedTransport owner targetNonzero small
        reserve).track.initial.ambientLeftClearance.bound =
      (ambientLeftAfterMove owner leftSmall).bound
  ambientRightBound :
    (reservedTransport owner targetNonzero small
        reserve).track.initial.ambientRightClearance.bound =
      (ambientRightAfterMove owner rightSmall).bound
  ambientBottomBound :
    (reservedTransport owner targetNonzero small
        reserve).track.initial.ambientBottomClearance.bound =
      (ambientBottomAfterMove owner bottomSmall).bound
  ambientTopBound :
    (reservedTransport owner targetNonzero small
        reserve).track.initial.ambientTopClearance.bound =
      (ambientTopAfterMove owner topSmall).bound
  clearanceBound :
    (reservedTransport owner targetNonzero small
        reserve).track.initial.clearance.bound =
      min (ambientLeftAfterMove owner leftSmall).bound
        (min (ambientRightAfterMove owner rightSmall).bound
          (min (ambientBottomAfterMove owner bottomSmall).bound
            (ambientTopAfterMove owner topSmall).bound))
  clearanceLeAmbientLeft :
    (reservedTransport owner targetNonzero small
        reserve).track.initial.clearance.bound <=
      (reservedTransport owner targetNonzero small
        reserve).track.initial.ambientLeftClearance.bound
  clearanceLeAmbientRight :
    (reservedTransport owner targetNonzero small
        reserve).track.initial.clearance.bound <=
      (reservedTransport owner targetNonzero small
        reserve).track.initial.ambientRightClearance.bound
  clearanceLeAmbientBottom :
    (reservedTransport owner targetNonzero small
        reserve).track.initial.clearance.bound <=
      (reservedTransport owner targetNonzero small
        reserve).track.initial.ambientBottomClearance.bound
  clearanceLeAmbientTop :
    (reservedTransport owner targetNonzero small
        reserve).track.initial.clearance.bound <=
      (reservedTransport owner targetNonzero small
        reserve).track.initial.ambientTopClearance.bound

/-- Cache the selected ambient-Rouché transport branch from its exact rational
comparisons. -/
theorem reservedTransportAmbientCache {source target : Gaussian}
    (owner : Owner source) (targetNonzero : target ≠ 0)
    (small : RFAP.ConstructiveGaussian.Gaussian.normSq (source - target) <
      owner.track.initial.clearance.bound) (reserve : Coordinate)
    (different : source ≠ target)
    (leftSmall : RFAP.ConstructiveGaussian.Gaussian.normSq (source - target) <
      owner.track.initial.ambientLeftClearance.bound)
    (rightSmall : RFAP.ConstructiveGaussian.Gaussian.normSq (source - target) <
      owner.track.initial.ambientRightClearance.bound)
    (bottomSmall : RFAP.ConstructiveGaussian.Gaussian.normSq (source - target) <
      owner.track.initial.ambientBottomClearance.bound)
    (topSmall : RFAP.ConstructiveGaussian.Gaussian.normSq (source - target) <
      owner.track.initial.ambientTopClearance.bound)
    (reserveSmall : reserve <
      (CCL.Riemann.SquareRootContinuation.transportedOwner
        owner.track.initial small).clearance.bound) :
    AmbientReservedTransportCache owner targetNonzero small reserve leftSmall
      rightSmall bottomSmall topSmall := by
  have selected : reservedTransport owner targetNonzero small reserve =
      ambientRoucheTransport owner targetNonzero small leftSmall rightSmall
        bottomSmall topSmall := by
    unfold reservedTransport
    rw [dif_neg different]
    dsimp only
    rw [dif_pos leftSmall, dif_pos rightSmall, dif_pos bottomSmall,
      dif_pos topSmall, dif_pos reserveSmall]
  refine
    { initialBox := by
        rw [selected]
        exact ambientRoucheTransport_initial_box owner targetNonzero small
          leftSmall rightSmall bottomSmall topSmall
      ambientBox := by
        rw [selected]
        exact ambientRoucheTransport_ambient owner targetNonzero small
          leftSmall rightSmall bottomSmall topSmall
      ambientLeftBound := by
        rw [selected]
        rfl
      ambientRightBound := by
        rw [selected]
        rfl
      ambientBottomBound := by
        rw [selected]
        rfl
      ambientTopBound := by
        rw [selected]
        rfl
      clearanceBound := by
        rw [selected]
        change (ambientAfterMoveClearance owner leftSmall rightSmall bottomSmall
          topSmall).bound = _
        exact ambientAfterMoveClearance_bound owner leftSmall rightSmall
          bottomSmall topSmall
      clearanceLeAmbientLeft := by
        rw [selected]
        change (ambientAfterMoveClearance owner leftSmall rightSmall bottomSmall
          topSmall).bound <= (ambientLeftAfterMove owner leftSmall).bound
        exact ambientAfterMoveClearance_le_left owner leftSmall rightSmall
          bottomSmall topSmall
      clearanceLeAmbientRight := by
        rw [selected]
        change (ambientAfterMoveClearance owner leftSmall rightSmall bottomSmall
          topSmall).bound <= (ambientRightAfterMove owner rightSmall).bound
        exact ambientAfterMoveClearance_le_right owner leftSmall rightSmall
          bottomSmall topSmall
      clearanceLeAmbientBottom := by
        rw [selected]
        change (ambientAfterMoveClearance owner leftSmall rightSmall bottomSmall
          topSmall).bound <= (ambientBottomAfterMove owner bottomSmall).bound
        exact ambientAfterMoveClearance_le_bottom owner leftSmall rightSmall
          bottomSmall topSmall
      clearanceLeAmbientTop := by
        rw [selected]
        change (ambientAfterMoveClearance owner leftSmall rightSmall bottomSmall
          topSmall).bound <= (ambientTopAfterMove owner topSmall).bound
        exact ambientAfterMoveClearance_le_top owner leftSmall rightSmall
          bottomSmall topSmall }

/-- The ambient branch cache packages the transported owner with the same
boundary-to-ambient dominance invariant. -/
theorem AmbientReservedTransportCache.ambientClearanceDominance
    {source target : Gaussian} {owner : Owner source}
    {targetNonzero : target ≠ 0}
    {small : RFAP.ConstructiveGaussian.Gaussian.normSq (source - target) <
      owner.track.initial.clearance.bound} {reserve : Coordinate}
    {leftSmall : RFAP.ConstructiveGaussian.Gaussian.normSq (source - target) <
      owner.track.initial.ambientLeftClearance.bound}
    {rightSmall : RFAP.ConstructiveGaussian.Gaussian.normSq (source - target) <
      owner.track.initial.ambientRightClearance.bound}
    {bottomSmall : RFAP.ConstructiveGaussian.Gaussian.normSq (source - target) <
      owner.track.initial.ambientBottomClearance.bound}
    {topSmall : RFAP.ConstructiveGaussian.Gaussian.normSq (source - target) <
      owner.track.initial.ambientTopClearance.bound}
    (cache : AmbientReservedTransportCache owner targetNonzero small reserve
      leftSmall rightSmall bottomSmall topSmall) :
    AmbientClearanceDominance
      (reservedTransport owner targetNonzero small reserve) :=
  ⟨cache.clearanceLeAmbientLeft, cache.clearanceLeAmbientRight,
    cache.clearanceLeAmbientBottom, cache.clearanceLeAmbientTop⟩

/-- The finite collection of source-polynomial and box bounds needed to use
the uniform quadratic Horner estimate on all four ambient lines.  The data is
stable under the inexpensive same-box transport. -/
structure QuadraticAmbientBudget {parameter : Gaussian}
    (owner : Owner parameter) : Prop where
  parameterNormSqLe :
    RFAP.ConstructiveGaussian.Gaussian.normSq parameter ≤ 256
  verticalIntervalSqLe :
    (RFAP.BoxClearance.verticalInterval owner.ambient).squareBound ≤ 16
  horizontalIntervalSqLe :
    (RFAP.BoxClearance.horizontalInterval owner.ambient).squareBound ≤ 16
  leftNonzero : owner.track.initial.box.xLower ≠ 0
  rightNonzero : owner.track.initial.box.xUpper ≠ 0
  bottomNonzero : owner.track.initial.box.yLower ≠ 0
  topNonzero : owner.track.initial.box.yUpper ≠ 0
  leftSqLe : owner.track.initial.box.xLower ^ 2 ≤ 16
  rightSqLe : owner.track.initial.box.xUpper ^ 2 ≤ 16
  bottomSqLe : owner.track.initial.box.yLower ^ 2 ≤ 16
  topSqLe : owner.track.initial.box.yUpper ^ 2 ≤ 16

/-- Build the quadratic Horner budget from one explicitly cached owner box.
This is the convenient entry point for direct and moving-recenter owners in
worked examples. -/
theorem quadraticAmbientBudget_of_box {parameter : Gaussian}
    (owner : Owner parameter) (box : Box)
    (initialBox : owner.track.initial.box = box)
    (ambientBox : owner.ambient = box)
    (parameterNormSqLe :
      RFAP.ConstructiveGaussian.Gaussian.normSq parameter ≤ 256)
    (leftNonzero : box.xLower ≠ 0) (rightNonzero : box.xUpper ≠ 0)
    (bottomNonzero : box.yLower ≠ 0) (topNonzero : box.yUpper ≠ 0)
    (leftSqLe : box.xLower ^ 2 ≤ 16)
    (rightSqLe : box.xUpper ^ 2 ≤ 16)
    (bottomSqLe : box.yLower ^ 2 ≤ 16)
    (topSqLe : box.yUpper ^ 2 ≤ 16) :
    QuadraticAmbientBudget owner := by
  refine
    { parameterNormSqLe := parameterNormSqLe
      verticalIntervalSqLe := ?_
      horizontalIntervalSqLe := ?_
      leftNonzero := ?_
      rightNonzero := ?_
      bottomNonzero := ?_
      topNonzero := ?_
      leftSqLe := ?_
      rightSqLe := ?_
      bottomSqLe := ?_
      topSqLe := ?_ }
  · rw [ambientBox]
    exact max_le bottomSqLe topSqLe
  · rw [ambientBox]
    exact max_le leftSqLe rightSqLe
  · rw [initialBox]
    exact leftNonzero
  · rw [initialBox]
    exact rightNonzero
  · rw [initialBox]
    exact bottomNonzero
  · rw [initialBox]
    exact topNonzero
  · rw [initialBox]
    exact leftSqLe
  · rw [initialBox]
    exact rightSqLe
  · rw [initialBox]
    exact bottomSqLe
  · rw [initialBox]
    exact topSqLe

/-- One fixed positive clearance floor shared by the explicit quadratic
examples.  Its displayed factors record the `1/2` Rouché margin and the
`65536` four-side Horner budget. -/
def quadraticAmbientTransportFloor : Coordinate :=
  ((1 : Coordinate) / 2) ^ 2 / (4 * 65536)

/-- Transport floor obtained from an explicitly cached residual margin.  The
fixed `quadraticAmbientTransportFloor` is the special case `margin = 1 / 2`;
worked paths may use smaller positive margins without discarding the same
finite Horner calculation. -/
def quadraticAmbientTransportFloorAt (margin : Coordinate) : Coordinate :=
  margin ^ 2 / (4 * 65536)

theorem quadraticAmbientTransportFloor_eq_at_half :
    quadraticAmbientTransportFloor =
      quadraticAmbientTransportFloorAt ((1 : Coordinate) / 2) := rfl

theorem quadraticAmbientTransportFloorAt_pos (margin : Coordinate)
    (positive : 0 < margin) :
    0 < quadraticAmbientTransportFloorAt margin := by
  unfold quadraticAmbientTransportFloorAt
  exact RFAP.ConstructiveFraction.div_pos_direct
    (RFAP.ConstructiveFraction.pow_pos_direct positive 2)
    (RFAP.ConstructiveFraction.mul_pos_direct (by decide)
      (RFAP.ConstructiveFraction.natCast_pos_direct
        (n := 65536) (by decide)))

theorem quadraticAmbientTransportFloor_pos :
    0 < quadraticAmbientTransportFloor := by
  unfold quadraticAmbientTransportFloor
  exact RFAP.ConstructiveFraction.div_pos_direct
    (RFAP.ConstructiveFraction.pow_pos_direct
      (RFAP.ConstructiveFraction.div_pos_direct (by decide) (by decide)) 2)
    (RFAP.ConstructiveFraction.mul_pos_direct (by decide)
      (RFAP.ConstructiveFraction.natCast_pos_direct
        (n := 65536) (by decide)))

private theorem quadraticAmbientTransportFloor_le_side
    (margin majorant : Coordinate)
    (marginLower : (1 : Coordinate) / 2 ≤ margin)
    (majorantOne : 1 ≤ majorant) (majorantLe : majorant ≤ 65536) :
    quadraticAmbientTransportFloor ≤ margin ^ 2 / (4 * majorant) := by
  have halfPositive : (0 : Coordinate) < 1 / 2 :=
    RFAP.ConstructiveFraction.div_pos_direct (by decide) (by decide)
  have marginNonnegative : 0 ≤ margin := halfPositive.le.trans marginLower
  have numeratorLe : ((1 : Coordinate) / 2) ^ 2 ≤ margin ^ 2 :=
    RFAP.ConstructiveFraction.pow_le_pow_direct halfPositive.le marginLower 2
  have majorantPositive : (0 : Coordinate) < majorant :=
    (show (0 : Coordinate) < 1 by decide).trans_le majorantOne
  have denominatorPositive : (0 : Coordinate) < 4 * majorant :=
    RFAP.ConstructiveFraction.mul_pos_direct (by decide) majorantPositive
  have denominatorLe : 4 * majorant ≤ (4 : Coordinate) * 65536 :=
    RFAP.ConstructiveFraction.mul_le_mul_of_nonneg_left_direct majorantLe
      (by decide)
  calc
    quadraticAmbientTransportFloor =
        ((1 : Coordinate) / 2) ^ 2 / (4 * 65536) := rfl
    _ ≤ ((1 : Coordinate) / 2) ^ 2 / (4 * majorant) :=
      RFAP.ConstructiveFraction.div_le_div_of_nonneg_left_direct
        (RFAP.ConstructiveFraction.sq_nonneg_direct ((1 : Coordinate) / 2))
        denominatorPositive denominatorLe
    _ ≤ margin ^ 2 / (4 * majorant) := by
      change ((1 : Coordinate) / 2) ^ 2 * (4 * majorant)⁻¹ ≤
        margin ^ 2 * (4 * majorant)⁻¹
      exact RFAP.ConstructiveFraction.mul_le_mul_of_nonneg_right_direct
        numeratorLe
        (RFAP.ConstructiveFraction.inv_pos_direct denominatorPositive).le

private theorem quadraticAmbientTransportFloorAt_le_side
    (floor margin majorant : Coordinate)
    (floorNonnegative : 0 ≤ floor) (floorLe : floor ≤ margin)
    (majorantOne : 1 ≤ majorant) (majorantLe : majorant ≤ 65536) :
    quadraticAmbientTransportFloorAt floor ≤
      margin ^ 2 / (4 * majorant) := by
  have marginNonnegative : 0 ≤ margin := floorNonnegative.trans floorLe
  have numeratorLe : floor ^ 2 ≤ margin ^ 2 :=
    RFAP.ConstructiveFraction.pow_le_pow_direct floorNonnegative floorLe 2
  have majorantPositive : (0 : Coordinate) < majorant :=
    (show (0 : Coordinate) < 1 by decide).trans_le majorantOne
  have denominatorPositive : (0 : Coordinate) < 4 * majorant :=
    RFAP.ConstructiveFraction.mul_pos_direct (by decide) majorantPositive
  have denominatorLe : 4 * majorant ≤ (4 : Coordinate) * 65536 :=
    RFAP.ConstructiveFraction.mul_le_mul_of_nonneg_left_direct majorantLe
      (by decide)
  calc
    quadraticAmbientTransportFloorAt floor =
        floor ^ 2 / (4 * 65536) := rfl
    _ ≤ floor ^ 2 / (4 * majorant) :=
      RFAP.ConstructiveFraction.div_le_div_of_nonneg_left_direct
        (RFAP.ConstructiveFraction.sq_nonneg_direct floor)
        denominatorPositive denominatorLe
    _ ≤ margin ^ 2 / (4 * majorant) := by
      change floor ^ 2 * (4 * majorant)⁻¹ ≤
        margin ^ 2 * (4 * majorant)⁻¹
      exact RFAP.ConstructiveFraction.mul_le_mul_of_nonneg_right_direct
        numeratorLe
        (RFAP.ConstructiveFraction.inv_pos_direct denominatorPositive).le

/-- Structural and quantitative result of ambient transport at an arbitrary
positive cached residual margin. -/
structure ParametricQuadraticAmbientTransportCache {source target : Gaussian}
    (owner : Owner source) (targetNonzero : target ≠ 0)
    (small : RFAP.ConstructiveGaussian.Gaussian.normSq (source - target) <
      owner.track.initial.clearance.bound)
    (marginFloor : Coordinate) where
  initialBox :
    (reservedTransport owner targetNonzero small 0).track.initial.box =
      owner.track.initial.box
  ambientBox :
    (reservedTransport owner targetNonzero small 0).ambient = owner.ambient
  clearanceFloor : quadraticAmbientTransportFloorAt marginFloor ≤
    (reservedTransport owner targetNonzero small 0).track.initial.clearance.bound
  ambientLeftQuarterSq :
    (reservedTransport owner targetNonzero small
        0).track.initial.ambientLeftClearance.bound ≤
      owner.track.initial.ambientLeftClearance.bound ^ 2 / 4
  clearanceQuarterSq :
    (reservedTransport owner targetNonzero small
        0).track.initial.clearance.bound ≤
      owner.track.initial.ambientLeftClearance.bound ^ 2 / 4
  dominance : AmbientClearanceDominance
    (reservedTransport owner targetNonzero small 0)
  budget : QuadraticAmbientBudget
    (reservedTransport owner targetNonzero small 0)

/-- A positive exact residual margin and the cached radius/parameter budgets
construct a successor cache without imposing the older half-unit floor. -/
theorem parametricQuadraticAmbientTransportCache {source target : Gaussian}
    (owner : Owner source) (targetNonzero : target ≠ 0)
    (small : RFAP.ConstructiveGaussian.Gaussian.normSq (source - target) <
      owner.track.initial.clearance.bound)
    (different : source ≠ target)
    (dominance : AmbientClearanceDominance owner)
    (marginFloor : Coordinate) (marginFloorPositive : 0 < marginFloor)
    (marginLower : marginFloor ≤
      owner.track.initial.clearance.bound -
        RFAP.ConstructiveGaussian.Gaussian.normSq (source - target))
    (budget : QuadraticAmbientBudget owner)
    (targetNormSqLe :
      RFAP.ConstructiveGaussian.Gaussian.normSq target ≤ 256) :
    ParametricQuadraticAmbientTransportCache owner targetNonzero small
      marginFloor := by
  let displacement :=
    RFAP.ConstructiveGaussian.Gaussian.normSq (source - target)
  have ambientSmall := dominance.ambientSmallness small
  have leftSmall := ambientSmall.1
  have rightSmall := ambientSmall.2.1
  have bottomSmall := ambientSmall.2.2.1
  have topSmall := ambientSmall.2.2.2
  have reserveSmall : (0 : Coordinate) <
      (CCL.Riemann.SquareRootContinuation.transportedOwner
        owner.track.initial small).clearance.bound :=
    (CCL.Riemann.SquareRootContinuation.transportedOwner
      owner.track.initial small).clearance.positive
  let ambientCache := reservedTransportAmbientCache owner targetNonzero small 0
    different leftSmall rightSmall bottomSmall topSmall reserveSmall
  have leftMargin : marginFloor ≤
      owner.track.initial.ambientLeftClearance.bound - displacement :=
    marginLower.trans
      (RFAP.ConstructiveFraction.sub_le_sub_right_direct dominance.left
        displacement)
  have rightMargin : marginFloor ≤
      owner.track.initial.ambientRightClearance.bound - displacement :=
    marginLower.trans
      (RFAP.ConstructiveFraction.sub_le_sub_right_direct dominance.right
        displacement)
  have bottomMargin : marginFloor ≤
      owner.track.initial.ambientBottomClearance.bound - displacement :=
    marginLower.trans
      (RFAP.ConstructiveFraction.sub_le_sub_right_direct dominance.bottom
        displacement)
  have topMargin : marginFloor ≤
      owner.track.initial.ambientTopClearance.bound - displacement :=
    marginLower.trans
      (RFAP.ConstructiveFraction.sub_le_sub_right_direct dominance.top
        displacement)
  have leftMajorantLe :
      RFAP.WindingHomotopy.boundarySideMajorant
        (CCL.PowerMonodromy.polynomial source
          CCL.Riemann.SquareRootSheets.degreeTwo)
        (RFAP.Winding.verticalBase owner.track.initial.box.xLower)
        RFAP.Winding.verticalDirection
        (RFAP.BoxClearance.verticalInterval owner.ambient) ≤ 65536 :=
    quadraticVerticalBoundarySideMajorant_le source
      owner.track.initial.box.xLower budget.leftNonzero
      (RFAP.BoxClearance.verticalInterval owner.ambient)
      budget.verticalIntervalSqLe budget.leftSqLe budget.parameterNormSqLe
  have rightMajorantLe :
      RFAP.WindingHomotopy.boundarySideMajorant
        (CCL.PowerMonodromy.polynomial source
          CCL.Riemann.SquareRootSheets.degreeTwo)
        (RFAP.Winding.verticalBase owner.track.initial.box.xUpper)
        RFAP.Winding.verticalDirection
        (RFAP.BoxClearance.verticalInterval owner.ambient) ≤ 65536 :=
    quadraticVerticalBoundarySideMajorant_le source
      owner.track.initial.box.xUpper budget.rightNonzero
      (RFAP.BoxClearance.verticalInterval owner.ambient)
      budget.verticalIntervalSqLe budget.rightSqLe budget.parameterNormSqLe
  have bottomMajorantLe :
      RFAP.WindingHomotopy.boundarySideMajorant
        (CCL.PowerMonodromy.polynomial source
          CCL.Riemann.SquareRootSheets.degreeTwo)
        (RFAP.Winding.horizontalBase owner.track.initial.box.yLower)
        RFAP.Winding.horizontalDirection
        (RFAP.BoxClearance.horizontalInterval owner.ambient) ≤ 65536 :=
    quadraticHorizontalBoundarySideMajorant_le source
      owner.track.initial.box.yLower budget.bottomNonzero
      (RFAP.BoxClearance.horizontalInterval owner.ambient)
      budget.horizontalIntervalSqLe budget.bottomSqLe budget.parameterNormSqLe
  have topMajorantLe :
      RFAP.WindingHomotopy.boundarySideMajorant
        (CCL.PowerMonodromy.polynomial source
          CCL.Riemann.SquareRootSheets.degreeTwo)
        (RFAP.Winding.horizontalBase owner.track.initial.box.yUpper)
        RFAP.Winding.horizontalDirection
        (RFAP.BoxClearance.horizontalInterval owner.ambient) ≤ 65536 :=
    quadraticHorizontalBoundarySideMajorant_le source
      owner.track.initial.box.yUpper budget.topNonzero
      (RFAP.BoxClearance.horizontalInterval owner.ambient)
      budget.horizontalIntervalSqLe budget.topSqLe budget.parameterNormSqLe
  have leftFloor : quadraticAmbientTransportFloorAt marginFloor ≤
      (ambientLeftAfterMove owner leftSmall).bound := by
    rw [ambientLeftAfterMove,
      CCL.PowerMonodromy.verticalClearanceAfterMove_bound]
    exact quadraticAmbientTransportFloorAt_le_side _ _ _
      marginFloorPositive.le leftMargin (le_max_left _ _) leftMajorantLe
  have rightFloor : quadraticAmbientTransportFloorAt marginFloor ≤
      (ambientRightAfterMove owner rightSmall).bound := by
    rw [ambientRightAfterMove,
      CCL.PowerMonodromy.verticalClearanceAfterMove_bound]
    exact quadraticAmbientTransportFloorAt_le_side _ _ _
      marginFloorPositive.le rightMargin (le_max_left _ _) rightMajorantLe
  have bottomFloor : quadraticAmbientTransportFloorAt marginFloor ≤
      (ambientBottomAfterMove owner bottomSmall).bound := by
    rw [ambientBottomAfterMove,
      CCL.PowerMonodromy.horizontalClearanceAfterMove_bound]
    exact quadraticAmbientTransportFloorAt_le_side _ _ _
      marginFloorPositive.le bottomMargin (le_max_left _ _) bottomMajorantLe
  have topFloor : quadraticAmbientTransportFloorAt marginFloor ≤
      (ambientTopAfterMove owner topSmall).bound := by
    rw [ambientTopAfterMove,
      CCL.PowerMonodromy.horizontalClearanceAfterMove_bound]
    exact quadraticAmbientTransportFloorAt_le_side _ _ _
      marginFloorPositive.le topMargin (le_max_left _ _) topMajorantLe
  refine
    { initialBox := ambientCache.initialBox
      ambientBox := ambientCache.ambientBox
      clearanceFloor := ?_
      ambientLeftQuarterSq := ?_
      clearanceQuarterSq := ?_
      dominance := ambientCache.ambientClearanceDominance
      budget := ?_ }
  · rw [ambientCache.clearanceBound]
    exact le_min leftFloor (le_min rightFloor (le_min bottomFloor topFloor))
  · rw [ambientCache.ambientLeftBound]
    exact ambientLeftAfterMove_bound_le_quarter_sq owner leftSmall
  · exact ambientCache.clearanceLeAmbientLeft.trans
      (ambientCache.ambientLeftBound.le.trans
        (ambientLeftAfterMove_bound_le_quarter_sq owner leftSmall))
  · refine
      { parameterNormSqLe := targetNormSqLe
        verticalIntervalSqLe := ?_
        horizontalIntervalSqLe := ?_
        leftNonzero := ?_
        rightNonzero := ?_
        bottomNonzero := ?_
        topNonzero := ?_
        leftSqLe := ?_
        rightSqLe := ?_
        bottomSqLe := ?_
        topSqLe := ?_ }
    · rw [ambientCache.ambientBox]
      exact budget.verticalIntervalSqLe
    · rw [ambientCache.ambientBox]
      exact budget.horizontalIntervalSqLe
    · rw [ambientCache.initialBox]
      exact budget.leftNonzero
    · rw [ambientCache.initialBox]
      exact budget.rightNonzero
    · rw [ambientCache.initialBox]
      exact budget.bottomNonzero
    · rw [ambientCache.initialBox]
      exact budget.topNonzero
    · rw [ambientCache.initialBox]
      exact budget.leftSqLe
    · rw [ambientCache.initialBox]
      exact budget.rightSqLe
    · rw [ambientCache.initialBox]
      exact budget.bottomSqLe
    · rw [ambientCache.initialBox]
      exact budget.topSqLe

/-- Structural and quantitative result of one uniform inexpensive quadratic
transport.  This cache is deliberately independent of the proof witnesses
used by the nested executable branch selection. -/
structure QuadraticAmbientTransportCache {source target : Gaussian}
    (owner : Owner source) (targetNonzero : target ≠ 0)
    (small : RFAP.ConstructiveGaussian.Gaussian.normSq (source - target) <
      owner.track.initial.clearance.bound) where
  initialBox :
    (reservedTransport owner targetNonzero small 0).track.initial.box =
      owner.track.initial.box
  ambientBox :
    (reservedTransport owner targetNonzero small 0).ambient = owner.ambient
  clearanceFloor : quadraticAmbientTransportFloor ≤
    (reservedTransport owner targetNonzero small 0).track.initial.clearance.bound
  ambientLeftQuarterSq :
    (reservedTransport owner targetNonzero small
        0).track.initial.ambientLeftClearance.bound ≤
      owner.track.initial.ambientLeftClearance.bound ^ 2 / 4
  clearanceQuarterSq :
    (reservedTransport owner targetNonzero small
        0).track.initial.clearance.bound ≤
      owner.track.initial.ambientLeftClearance.bound ^ 2 / 4
  dominance : AmbientClearanceDominance
    (reservedTransport owner targetNonzero small 0)
  budget : QuadraticAmbientBudget
    (reservedTransport owner targetNonzero small 0)

/-- A half-unit residual margin and the cached radius-`4`/parameter-`16`
budgets construct the complete successor cache in one step. -/
theorem quadraticAmbientTransportCache {source target : Gaussian}
    (owner : Owner source) (targetNonzero : target ≠ 0)
    (small : RFAP.ConstructiveGaussian.Gaussian.normSq (source - target) <
      owner.track.initial.clearance.bound)
    (different : source ≠ target)
    (dominance : AmbientClearanceDominance owner)
    (marginLower : (1 : Coordinate) / 2 ≤
      owner.track.initial.clearance.bound -
        RFAP.ConstructiveGaussian.Gaussian.normSq (source - target))
    (budget : QuadraticAmbientBudget owner)
    (targetNormSqLe :
      RFAP.ConstructiveGaussian.Gaussian.normSq target ≤ 256) :
    QuadraticAmbientTransportCache owner targetNonzero small := by
  let displacement :=
    RFAP.ConstructiveGaussian.Gaussian.normSq (source - target)
  have ambientSmall := dominance.ambientSmallness small
  have leftSmall := ambientSmall.1
  have rightSmall := ambientSmall.2.1
  have bottomSmall := ambientSmall.2.2.1
  have topSmall := ambientSmall.2.2.2
  have reserveSmall : (0 : Coordinate) <
      (CCL.Riemann.SquareRootContinuation.transportedOwner
        owner.track.initial small).clearance.bound :=
    (CCL.Riemann.SquareRootContinuation.transportedOwner
      owner.track.initial small).clearance.positive
  let ambientCache := reservedTransportAmbientCache owner targetNonzero small 0
    different leftSmall rightSmall bottomSmall topSmall reserveSmall
  have leftMargin : (1 : Coordinate) / 2 ≤
      owner.track.initial.ambientLeftClearance.bound - displacement :=
    marginLower.trans
      (RFAP.ConstructiveFraction.sub_le_sub_right_direct dominance.left
        displacement)
  have rightMargin : (1 : Coordinate) / 2 ≤
      owner.track.initial.ambientRightClearance.bound - displacement :=
    marginLower.trans
      (RFAP.ConstructiveFraction.sub_le_sub_right_direct dominance.right
        displacement)
  have bottomMargin : (1 : Coordinate) / 2 ≤
      owner.track.initial.ambientBottomClearance.bound - displacement :=
    marginLower.trans
      (RFAP.ConstructiveFraction.sub_le_sub_right_direct dominance.bottom
        displacement)
  have topMargin : (1 : Coordinate) / 2 ≤
      owner.track.initial.ambientTopClearance.bound - displacement :=
    marginLower.trans
      (RFAP.ConstructiveFraction.sub_le_sub_right_direct dominance.top
        displacement)
  have leftMajorantLe :
      RFAP.WindingHomotopy.boundarySideMajorant
        (CCL.PowerMonodromy.polynomial source
          CCL.Riemann.SquareRootSheets.degreeTwo)
        (RFAP.Winding.verticalBase owner.track.initial.box.xLower)
        RFAP.Winding.verticalDirection
        (RFAP.BoxClearance.verticalInterval owner.ambient) ≤ 65536 :=
    quadraticVerticalBoundarySideMajorant_le source
      owner.track.initial.box.xLower budget.leftNonzero
      (RFAP.BoxClearance.verticalInterval owner.ambient)
      budget.verticalIntervalSqLe budget.leftSqLe budget.parameterNormSqLe
  have rightMajorantLe :
      RFAP.WindingHomotopy.boundarySideMajorant
        (CCL.PowerMonodromy.polynomial source
          CCL.Riemann.SquareRootSheets.degreeTwo)
        (RFAP.Winding.verticalBase owner.track.initial.box.xUpper)
        RFAP.Winding.verticalDirection
        (RFAP.BoxClearance.verticalInterval owner.ambient) ≤ 65536 :=
    quadraticVerticalBoundarySideMajorant_le source
      owner.track.initial.box.xUpper budget.rightNonzero
      (RFAP.BoxClearance.verticalInterval owner.ambient)
      budget.verticalIntervalSqLe budget.rightSqLe budget.parameterNormSqLe
  have bottomMajorantLe :
      RFAP.WindingHomotopy.boundarySideMajorant
        (CCL.PowerMonodromy.polynomial source
          CCL.Riemann.SquareRootSheets.degreeTwo)
        (RFAP.Winding.horizontalBase owner.track.initial.box.yLower)
        RFAP.Winding.horizontalDirection
        (RFAP.BoxClearance.horizontalInterval owner.ambient) ≤ 65536 :=
    quadraticHorizontalBoundarySideMajorant_le source
      owner.track.initial.box.yLower budget.bottomNonzero
      (RFAP.BoxClearance.horizontalInterval owner.ambient)
      budget.horizontalIntervalSqLe budget.bottomSqLe budget.parameterNormSqLe
  have topMajorantLe :
      RFAP.WindingHomotopy.boundarySideMajorant
        (CCL.PowerMonodromy.polynomial source
          CCL.Riemann.SquareRootSheets.degreeTwo)
        (RFAP.Winding.horizontalBase owner.track.initial.box.yUpper)
        RFAP.Winding.horizontalDirection
        (RFAP.BoxClearance.horizontalInterval owner.ambient) ≤ 65536 :=
    quadraticHorizontalBoundarySideMajorant_le source
      owner.track.initial.box.yUpper budget.topNonzero
      (RFAP.BoxClearance.horizontalInterval owner.ambient)
      budget.horizontalIntervalSqLe budget.topSqLe budget.parameterNormSqLe
  have leftFloor : quadraticAmbientTransportFloor ≤
      (ambientLeftAfterMove owner leftSmall).bound := by
    rw [ambientLeftAfterMove,
      CCL.PowerMonodromy.verticalClearanceAfterMove_bound]
    exact quadraticAmbientTransportFloor_le_side _ _ leftMargin
      (le_max_left _ _) leftMajorantLe
  have rightFloor : quadraticAmbientTransportFloor ≤
      (ambientRightAfterMove owner rightSmall).bound := by
    rw [ambientRightAfterMove,
      CCL.PowerMonodromy.verticalClearanceAfterMove_bound]
    exact quadraticAmbientTransportFloor_le_side _ _ rightMargin
      (le_max_left _ _) rightMajorantLe
  have bottomFloor : quadraticAmbientTransportFloor ≤
      (ambientBottomAfterMove owner bottomSmall).bound := by
    rw [ambientBottomAfterMove,
      CCL.PowerMonodromy.horizontalClearanceAfterMove_bound]
    exact quadraticAmbientTransportFloor_le_side _ _ bottomMargin
      (le_max_left _ _) bottomMajorantLe
  have topFloor : quadraticAmbientTransportFloor ≤
      (ambientTopAfterMove owner topSmall).bound := by
    rw [ambientTopAfterMove,
      CCL.PowerMonodromy.horizontalClearanceAfterMove_bound]
    exact quadraticAmbientTransportFloor_le_side _ _ topMargin
      (le_max_left _ _) topMajorantLe
  refine
    { initialBox := ambientCache.initialBox
      ambientBox := ambientCache.ambientBox
      clearanceFloor := ?_
      ambientLeftQuarterSq := ?_
      clearanceQuarterSq := ?_
      dominance := ambientCache.ambientClearanceDominance
      budget := ?_ }
  · rw [ambientCache.clearanceBound]
    exact le_min leftFloor (le_min rightFloor (le_min bottomFloor topFloor))
  · rw [ambientCache.ambientLeftBound]
    exact ambientLeftAfterMove_bound_le_quarter_sq owner leftSmall
  · exact ambientCache.clearanceLeAmbientLeft.trans
      (ambientCache.ambientLeftBound.le.trans
        (ambientLeftAfterMove_bound_le_quarter_sq owner leftSmall))
  · refine
      { parameterNormSqLe := targetNormSqLe
        verticalIntervalSqLe := ?_
        horizontalIntervalSqLe := ?_
        leftNonzero := ?_
        rightNonzero := ?_
        bottomNonzero := ?_
        topNonzero := ?_
        leftSqLe := ?_
        rightSqLe := ?_
        bottomSqLe := ?_
        topSqLe := ?_ }
    · rw [ambientCache.ambientBox]
      exact budget.verticalIntervalSqLe
    · rw [ambientCache.ambientBox]
      exact budget.horizontalIntervalSqLe
    · rw [ambientCache.initialBox]
      exact budget.leftNonzero
    · rw [ambientCache.initialBox]
      exact budget.rightNonzero
    · rw [ambientCache.initialBox]
      exact budget.bottomNonzero
    · rw [ambientCache.initialBox]
      exact budget.topNonzero
    · rw [ambientCache.initialBox]
      exact budget.leftSqLe
    · rw [ambientCache.initialBox]
      exact budget.rightSqLe
    · rw [ambientCache.initialBox]
      exact budget.bottomSqLe
    · rw [ambientCache.initialBox]
      exact budget.topSqLe

/-- Both executable branches retain the source box or return a certified
strict descendant. -/
theorem reservedTransport_initial_box_refines {source target : Gaussian}
    (owner : Owner source) (targetNonzero : target ≠ 0)
    (small : RFAP.ConstructiveGaussian.Gaussian.normSq (source - target) <
      owner.track.initial.clearance.bound) (reserve : Coordinate) :
    (reservedTransport owner targetNonzero small reserve).track.initial.box.Refines
      owner.track.initial.box := by
  unfold reservedTransport
  by_cases same : source = target
  · rw [dif_pos same]
    subst target
    exact RFAP.Boxes.Box.refines_refl _
  · rw [dif_neg same]
    dsimp only
    by_cases leftSmall :
        RFAP.ConstructiveGaussian.Gaussian.normSq (source - target) <
          owner.track.initial.ambientLeftClearance.bound
    · rw [dif_pos leftSmall]
      by_cases rightSmall :
          RFAP.ConstructiveGaussian.Gaussian.normSq (source - target) <
            owner.track.initial.ambientRightClearance.bound
      · rw [dif_pos rightSmall]
        by_cases bottomSmall :
            RFAP.ConstructiveGaussian.Gaussian.normSq (source - target) <
              owner.track.initial.ambientBottomClearance.bound
        · rw [dif_pos bottomSmall]
          by_cases topSmall :
              RFAP.ConstructiveGaussian.Gaussian.normSq (source - target) <
                owner.track.initial.ambientTopClearance.bound
          · rw [dif_pos topSmall]
            by_cases reserveSmall : reserve <
                (CCL.Riemann.SquareRootContinuation.transportedOwner
                  owner.track.initial small).clearance.bound
            · rw [dif_pos reserveSmall]
              rw [ambientRoucheTransport_initial_box]
              exact RFAP.Boxes.Box.refines_refl _
            · rw [dif_neg reserveSmall]
              exact resultantReservedTransport_initial_box_refines owner
                targetNonzero small reserve
          · rw [dif_neg topSmall]
            exact resultantReservedTransport_initial_box_refines owner
              targetNonzero small reserve
        · rw [dif_neg bottomSmall]
          exact resultantReservedTransport_initial_box_refines owner
            targetNonzero small reserve
      · rw [dif_neg rightSmall]
        exact resultantReservedTransport_initial_box_refines owner targetNonzero
          small reserve
    · rw [dif_neg leftSmall]
      exact resultantReservedTransport_initial_box_refines owner targetNonzero
        small reserve

/-- The cheap Rouché branch and the resultant fallback both name the same
target occurrence as generic Newton continuation. -/
def reservedTransport_generic_relation {source target : Gaussian}
    (owner : Owner source) (targetNonzero : target ≠ 0)
    (small : RFAP.ConstructiveGaussian.Gaussian.normSq (source - target) <
      owner.track.initial.clearance.bound) (reserve : Coordinate) :
    PSum
      (reservedTransport owner targetNonzero small reserve =
        owner.advance targetNonzero small)
      (DirectPresentationRelation owner targetNonzero small
        (reservedTransport owner targetNonzero small reserve)) := by
  unfold reservedTransport
  by_cases same : source = target
  · rw [dif_pos same]
    subst target
    exact PSum.inr
      { parent := owner
        genericStrictParent :=
          CCL.Riemann.SquareRootContinuation.continuedTrack_initial_strict_source
            targetNonzero owner.track.initial small
        resultRefinesParent := RFAP.Boxes.Box.refines_refl _ }
  · rw [dif_neg same]
    dsimp only
    by_cases leftSmall :
        RFAP.ConstructiveGaussian.Gaussian.normSq (source - target) <
          owner.track.initial.ambientLeftClearance.bound
    · rw [dif_pos leftSmall]
      by_cases rightSmall :
          RFAP.ConstructiveGaussian.Gaussian.normSq (source - target) <
            owner.track.initial.ambientRightClearance.bound
      · rw [dif_pos rightSmall]
        by_cases bottomSmall :
            RFAP.ConstructiveGaussian.Gaussian.normSq (source - target) <
              owner.track.initial.ambientBottomClearance.bound
        · rw [dif_pos bottomSmall]
          by_cases topSmall :
              RFAP.ConstructiveGaussian.Gaussian.normSq (source - target) <
                owner.track.initial.ambientTopClearance.bound
          · rw [dif_pos topSmall]
            by_cases reserveSmall : reserve <
                (CCL.Riemann.SquareRootContinuation.transportedOwner
                  owner.track.initial small).clearance.bound
            · rw [dif_pos reserveSmall]
              exact PSum.inr
                { parent := ambientRoucheTransport owner targetNonzero small
                    leftSmall rightSmall bottomSmall topSmall
                  genericStrictParent := by
                    rw [ambientRoucheTransport_initial_box]
                    exact CCL.Riemann.SquareRootContinuation.continuedTrack_initial_strict_source
                      targetNonzero owner.track.initial small
                  resultRefinesParent := RFAP.Boxes.Box.refines_refl _ }
            · rw [dif_neg reserveSmall]
              exact resultantReservedTransport_generic_relation owner
                targetNonzero small reserve
          · rw [dif_neg topSmall]
            exact resultantReservedTransport_generic_relation owner
              targetNonzero small reserve
        · rw [dif_neg bottomSmall]
          exact resultantReservedTransport_generic_relation owner targetNonzero
            small reserve
      · rw [dif_neg rightSmall]
        exact resultantReservedTransport_generic_relation owner targetNonzero
          small reserve
    · rw [dif_neg leftSmall]
      exact resultantReservedTransport_generic_relation owner targetNonzero
        small reserve

/-- Fast same-box transport with only positivity reserved.  Since every exact
boundary clearance is positive, this takes the direct branch whenever all
four side resultants are nonzero. -/
def directTransport {source target : Gaussian}
    (owner : Owner source) (targetNonzero : target ≠ 0)
    (small : RFAP.ConstructiveGaussian.Gaussian.normSq (source - target) <
      owner.track.initial.clearance.bound) : Owner target :=
  reservedTransport owner targetNonzero small 0

theorem directTransport_initial_box_refines {source target : Gaussian}
    (owner : Owner source) (targetNonzero : target ≠ 0)
    (small : RFAP.ConstructiveGaussian.Gaussian.normSq (source - target) <
      owner.track.initial.clearance.bound) :
    (directTransport owner targetNonzero small).track.initial.box.Refines
      owner.track.initial.box := by
  exact reservedTransport_initial_box_refines owner targetNonzero small 0

/-- Computational branch data: either fast transport is generic transport,
or the generic Newton band is a strict descendant of its same-box direct
presentation. -/
def directTransport_generic_relation {source target : Gaussian}
    (owner : Owner source) (targetNonzero : target ≠ 0)
    (small : RFAP.ConstructiveGaussian.Gaussian.normSq (source - target) <
      owner.track.initial.clearance.bound) :
    PSum
      (directTransport owner targetNonzero small =
        owner.advance targetNonzero small)
      (DirectPresentationRelation owner targetNonzero small
        (directTransport owner targetNonzero small)) := by
  exact reservedTransport_generic_relation owner targetNonzero small 0

attribute [irreducible] reservedTransport directTransport

/-- Keep the stronger of two independently certified boundary clearances on
the same rational box. -/
private def maxBoundaryClearance
    {polynomial : GaussianPolynomial} {box : Box}
    (first second : RFAP.BoxClearance.BoundaryClearance polynomial box) :
    RFAP.BoxClearance.BoundaryClearance polynomial box where
  bound := max first.bound second.bound
  positive := first.positive.trans_le (le_max_left _ _)
  lower := by
    intro point boundary
    exact max_le (first.lower point boundary) (second.lower point boundary)

/-- Repackage one quadratic owner on its existing winding-one box using exact
side resultants.  Failure of any determinant check returns the original
owner, so this finite acceleration never weakens the generic construction. -/
private def strengthenQuadraticOwnerImpl {parameter : Gaussian}
    (owner : Owner parameter) : Owner parameter :=
  let box := owner.track.initial.box
  if leftNonzero :
      CCL.Riemann.SquareRootContinuationChain.Owner.verticalDeterminant
          parameter box.xLower ≠ 0 then
    if rightNonzero :
        CCL.Riemann.SquareRootContinuationChain.Owner.verticalDeterminant
            parameter box.xUpper ≠ 0 then
      if bottomNonzero :
          CCL.Riemann.SquareRootContinuationChain.Owner.horizontalDeterminant
              parameter box.yLower ≠ 0 then
        if topNonzero :
            CCL.Riemann.SquareRootContinuationChain.Owner.horizontalDeterminant
                parameter box.yUpper ≠ 0 then
          let direct := directBoundaryClearance parameter box leftNonzero
            rightNonzero bottomNonzero topNonzero
          let clearance := maxBoundaryClearance
            owner.track.initial.clearance direct
          let initial : RFAP.ShrinkingTrack.WindingOneState
              (rootPolynomial parameter) box :=
            { box := box
              refinesAmbient := RFAP.Boxes.Box.refines_refl box
              proper := owner.track.initial.proper
              clearance := clearance
              rawWindingFour := owner.track.initial.rawWindingFour
              ambientLeftClearance :=
                RFAP.BoxClearance.leftOfBoundary clearance
              ambientRightClearance :=
                RFAP.BoxClearance.rightOfBoundary clearance
              ambientBottomClearance :=
                RFAP.BoxClearance.bottomOfBoundary clearance
              ambientTopClearance :=
                RFAP.BoxClearance.topOfBoundary clearance }
          { parameterNonzero := owner.parameterNonzero
            ambient := box
            track := deferredTrack owner.parameterNonzero initial }
        else owner
      else owner
    else owner
  else owner

private theorem strengthenQuadraticOwnerImpl_initial_box {parameter : Gaussian}
    (owner : Owner parameter) :
    (strengthenQuadraticOwnerImpl owner).track.initial.box =
      owner.track.initial.box := by
  unfold strengthenQuadraticOwnerImpl
  dsimp only
  by_cases leftNonzero :
      CCL.Riemann.SquareRootContinuationChain.Owner.verticalDeterminant
        parameter owner.track.initial.box.xLower ≠ 0
  · rw [dif_pos leftNonzero]
    by_cases rightNonzero :
        CCL.Riemann.SquareRootContinuationChain.Owner.verticalDeterminant
          parameter owner.track.initial.box.xUpper ≠ 0
    · rw [dif_pos rightNonzero]
      by_cases bottomNonzero :
          CCL.Riemann.SquareRootContinuationChain.Owner.horizontalDeterminant
            parameter owner.track.initial.box.yLower ≠ 0
      · rw [dif_pos bottomNonzero]
        by_cases topNonzero :
            CCL.Riemann.SquareRootContinuationChain.Owner.horizontalDeterminant
              parameter owner.track.initial.box.yUpper ≠ 0
        · rw [dif_pos topNonzero]
          rfl
        · rw [dif_neg topNonzero]
      · rw [dif_neg bottomNonzero]
    · rw [dif_neg rightNonzero]
  · rw [dif_neg leftNonzero]

private theorem strengthenQuadraticOwnerImpl_ambient_refines
    {parameter : Gaussian} (owner : Owner parameter) :
    (strengthenQuadraticOwnerImpl owner).ambient.Refines owner.ambient := by
  unfold strengthenQuadraticOwnerImpl
  dsimp only
  by_cases leftNonzero :
      CCL.Riemann.SquareRootContinuationChain.Owner.verticalDeterminant
        parameter owner.track.initial.box.xLower ≠ 0
  · rw [dif_pos leftNonzero]
    by_cases rightNonzero :
        CCL.Riemann.SquareRootContinuationChain.Owner.verticalDeterminant
          parameter owner.track.initial.box.xUpper ≠ 0
    · rw [dif_pos rightNonzero]
      by_cases bottomNonzero :
          CCL.Riemann.SquareRootContinuationChain.Owner.horizontalDeterminant
            parameter owner.track.initial.box.yLower ≠ 0
      · rw [dif_pos bottomNonzero]
        by_cases topNonzero :
            CCL.Riemann.SquareRootContinuationChain.Owner.horizontalDeterminant
              parameter owner.track.initial.box.yUpper ≠ 0
        · rw [dif_pos topNonzero]
          exact owner.track.initial.refinesAmbient
        · rw [dif_neg topNonzero]
          exact RFAP.Boxes.Box.refines_refl _
      · rw [dif_neg bottomNonzero]
        exact RFAP.Boxes.Box.refines_refl _
    · rw [dif_neg rightNonzero]
      exact RFAP.Boxes.Box.refines_refl _
  · rw [dif_neg leftNonzero]
    exact RFAP.Boxes.Box.refines_refl _

private theorem strengthenQuadraticOwnerImpl_clearance_le
    {parameter : Gaussian} (owner : Owner parameter) :
    owner.track.initial.clearance.bound ≤
      (strengthenQuadraticOwnerImpl owner).track.initial.clearance.bound := by
  unfold strengthenQuadraticOwnerImpl
  dsimp only
  by_cases leftNonzero :
      CCL.Riemann.SquareRootContinuationChain.Owner.verticalDeterminant
        parameter owner.track.initial.box.xLower ≠ 0
  · rw [dif_pos leftNonzero]
    by_cases rightNonzero :
        CCL.Riemann.SquareRootContinuationChain.Owner.verticalDeterminant
          parameter owner.track.initial.box.xUpper ≠ 0
    · rw [dif_pos rightNonzero]
      by_cases bottomNonzero :
          CCL.Riemann.SquareRootContinuationChain.Owner.horizontalDeterminant
            parameter owner.track.initial.box.yLower ≠ 0
      · rw [dif_pos bottomNonzero]
        by_cases topNonzero :
            CCL.Riemann.SquareRootContinuationChain.Owner.horizontalDeterminant
              parameter owner.track.initial.box.yUpper ≠ 0
        · rw [dif_pos topNonzero]
          exact le_max_left _ _
        · rw [dif_neg topNonzero]
      · rw [dif_neg bottomNonzero]
    · rw [dif_neg rightNonzero]
  · rw [dif_neg leftNonzero]

/-- When all four exact side resultants are nonzero, the opaque strengthened
owner retains at least the corresponding direct resultant clearance. -/
private theorem strengthenQuadraticOwnerImpl_direct_clearance_le
    {parameter : Gaussian} (owner : Owner parameter)
    (leftNonzero :
      CCL.Riemann.SquareRootContinuationChain.Owner.verticalDeterminant
        parameter owner.track.initial.box.xLower ≠ 0)
    (rightNonzero :
      CCL.Riemann.SquareRootContinuationChain.Owner.verticalDeterminant
        parameter owner.track.initial.box.xUpper ≠ 0)
    (bottomNonzero :
      CCL.Riemann.SquareRootContinuationChain.Owner.horizontalDeterminant
        parameter owner.track.initial.box.yLower ≠ 0)
    (topNonzero :
      CCL.Riemann.SquareRootContinuationChain.Owner.horizontalDeterminant
        parameter owner.track.initial.box.yUpper ≠ 0) :
    (directBoundaryClearance parameter owner.track.initial.box leftNonzero
        rightNonzero bottomNonzero topNonzero).bound ≤
      (strengthenQuadraticOwnerImpl owner).track.initial.clearance.bound := by
  unfold strengthenQuadraticOwnerImpl
  dsimp only
  rw [dif_pos leftNonzero, dif_pos rightNonzero, dif_pos bottomNonzero,
    dif_pos topNonzero]
  exact le_max_right _ _

/-- The exact cached clearance calculation on the successful direct branch. -/
private theorem strengthenQuadraticOwnerImpl_clearance_eq_max
    {parameter : Gaussian} (owner : Owner parameter)
    (leftNonzero :
      CCL.Riemann.SquareRootContinuationChain.Owner.verticalDeterminant
        parameter owner.track.initial.box.xLower ≠ 0)
    (rightNonzero :
      CCL.Riemann.SquareRootContinuationChain.Owner.verticalDeterminant
        parameter owner.track.initial.box.xUpper ≠ 0)
    (bottomNonzero :
      CCL.Riemann.SquareRootContinuationChain.Owner.horizontalDeterminant
        parameter owner.track.initial.box.yLower ≠ 0)
    (topNonzero :
      CCL.Riemann.SquareRootContinuationChain.Owner.horizontalDeterminant
        parameter owner.track.initial.box.yUpper ≠ 0) :
    (strengthenQuadraticOwnerImpl owner).track.initial.clearance.bound =
      max owner.track.initial.clearance.bound
        (directBoundaryClearance parameter owner.track.initial.box leftNonzero
          rightNonzero bottomNonzero topNonzero).bound := by
  unfold strengthenQuadraticOwnerImpl
  dsimp only
  rw [dif_pos leftNonzero, dif_pos rightNonzero, dif_pos bottomNonzero,
    dif_pos topNonzero]
  rfl

private theorem strengthenQuadraticOwnerImpl_ambient_clearance_eq
    {parameter : Gaussian} (owner : Owner parameter)
    (leftNonzero :
      CCL.Riemann.SquareRootContinuationChain.Owner.verticalDeterminant
        parameter owner.track.initial.box.xLower ≠ 0)
    (rightNonzero :
      CCL.Riemann.SquareRootContinuationChain.Owner.verticalDeterminant
        parameter owner.track.initial.box.xUpper ≠ 0)
    (bottomNonzero :
      CCL.Riemann.SquareRootContinuationChain.Owner.horizontalDeterminant
        parameter owner.track.initial.box.yLower ≠ 0)
    (topNonzero :
      CCL.Riemann.SquareRootContinuationChain.Owner.horizontalDeterminant
        parameter owner.track.initial.box.yUpper ≠ 0) :
    let strengthened := strengthenQuadraticOwnerImpl owner
    strengthened.track.initial.ambientLeftClearance.bound =
        strengthened.track.initial.clearance.bound ∧
      strengthened.track.initial.ambientRightClearance.bound =
          strengthened.track.initial.clearance.bound ∧
        strengthened.track.initial.ambientBottomClearance.bound =
            strengthened.track.initial.clearance.bound ∧
          strengthened.track.initial.ambientTopClearance.bound =
            strengthened.track.initial.clearance.bound := by
  unfold strengthenQuadraticOwnerImpl
  dsimp only
  rw [dif_pos leftNonzero, dif_pos rightNonzero, dif_pos bottomNonzero,
    dif_pos topNonzero]
  exact ⟨rfl, rfl, rfl, rfl⟩

private theorem strengthenQuadraticOwnerImpl_ambientClearanceDominance
    {parameter : Gaussian} (owner : Owner parameter)
    (dominance : AmbientClearanceDominance owner) :
    AmbientClearanceDominance (strengthenQuadraticOwnerImpl owner) := by
  unfold strengthenQuadraticOwnerImpl
  dsimp only
  by_cases leftNonzero :
      CCL.Riemann.SquareRootContinuationChain.Owner.verticalDeterminant
        parameter owner.track.initial.box.xLower ≠ 0
  · rw [dif_pos leftNonzero]
    by_cases rightNonzero :
        CCL.Riemann.SquareRootContinuationChain.Owner.verticalDeterminant
          parameter owner.track.initial.box.xUpper ≠ 0
    · rw [dif_pos rightNonzero]
      by_cases bottomNonzero :
          CCL.Riemann.SquareRootContinuationChain.Owner.horizontalDeterminant
            parameter owner.track.initial.box.yLower ≠ 0
      · rw [dif_pos bottomNonzero]
        by_cases topNonzero :
            CCL.Riemann.SquareRootContinuationChain.Owner.horizontalDeterminant
              parameter owner.track.initial.box.yUpper ≠ 0
        · rw [dif_pos topNonzero]
          exact ⟨le_rfl, le_rfl, le_rfl, le_rfl⟩
        · rw [dif_neg topNonzero]
          exact dominance
      · rw [dif_neg bottomNonzero]
        exact dominance
    · rw [dif_neg rightNonzero]
      exact dominance
  · rw [dif_neg leftNonzero]
    exact dominance

/-- The strengthened value and the two facts needed by every downstream
consumer.  Keeping this as one package lets the executable implementation be
opaque to dependent conversion without hiding any certified behavior. -/
private structure Strengthening {parameter : Gaussian}
    (original : Owner parameter) where
  value : Owner parameter
  initialBox : value.track.initial.box = original.track.initial.box
  ambientRefines : value.ambient.Refines original.ambient
  clearanceLe : original.track.initial.clearance.bound ≤
    value.track.initial.clearance.bound
  directClearanceLe :
    forall
      (leftNonzero :
        CCL.Riemann.SquareRootContinuationChain.Owner.verticalDeterminant
          parameter original.track.initial.box.xLower ≠ 0)
      (rightNonzero :
        CCL.Riemann.SquareRootContinuationChain.Owner.verticalDeterminant
          parameter original.track.initial.box.xUpper ≠ 0)
      (bottomNonzero :
        CCL.Riemann.SquareRootContinuationChain.Owner.horizontalDeterminant
          parameter original.track.initial.box.yLower ≠ 0)
      (topNonzero :
        CCL.Riemann.SquareRootContinuationChain.Owner.horizontalDeterminant
          parameter original.track.initial.box.yUpper ≠ 0),
      (directBoundaryClearance parameter original.track.initial.box
          leftNonzero rightNonzero bottomNonzero topNonzero).bound ≤
        value.track.initial.clearance.bound
  clearanceEqMax :
    forall
      (leftNonzero :
        CCL.Riemann.SquareRootContinuationChain.Owner.verticalDeterminant
          parameter original.track.initial.box.xLower ≠ 0)
      (rightNonzero :
        CCL.Riemann.SquareRootContinuationChain.Owner.verticalDeterminant
          parameter original.track.initial.box.xUpper ≠ 0)
      (bottomNonzero :
        CCL.Riemann.SquareRootContinuationChain.Owner.horizontalDeterminant
          parameter original.track.initial.box.yLower ≠ 0)
      (topNonzero :
        CCL.Riemann.SquareRootContinuationChain.Owner.horizontalDeterminant
          parameter original.track.initial.box.yUpper ≠ 0),
      value.track.initial.clearance.bound =
        max original.track.initial.clearance.bound
          (directBoundaryClearance parameter original.track.initial.box
            leftNonzero rightNonzero bottomNonzero topNonzero).bound
  ambientClearanceEq :
    forall
      (_leftNonzero :
        CCL.Riemann.SquareRootContinuationChain.Owner.verticalDeterminant
          parameter original.track.initial.box.xLower ≠ 0)
      (_rightNonzero :
        CCL.Riemann.SquareRootContinuationChain.Owner.verticalDeterminant
          parameter original.track.initial.box.xUpper ≠ 0)
      (_bottomNonzero :
        CCL.Riemann.SquareRootContinuationChain.Owner.horizontalDeterminant
          parameter original.track.initial.box.yLower ≠ 0)
      (_topNonzero :
        CCL.Riemann.SquareRootContinuationChain.Owner.horizontalDeterminant
          parameter original.track.initial.box.yUpper ≠ 0),
      value.track.initial.ambientLeftClearance.bound =
          value.track.initial.clearance.bound ∧
        value.track.initial.ambientRightClearance.bound =
            value.track.initial.clearance.bound ∧
          value.track.initial.ambientBottomClearance.bound =
              value.track.initial.clearance.bound ∧
            value.track.initial.ambientTopClearance.bound =
              value.track.initial.clearance.bound
  ambientDominance : AmbientClearanceDominance original ->
    AmbientClearanceDominance value

/-- Executable opacity boundary for the large quadratic owner constructor.
The code generator retains the implementation, while elaboration consumes
only the two stored interface proofs. -/
private opaque certifiedStrengthening {parameter : Gaussian}
    (owner : Owner parameter) : Strengthening owner :=
  { value := strengthenQuadraticOwnerImpl owner
    initialBox := strengthenQuadraticOwnerImpl_initial_box owner
    ambientRefines := strengthenQuadraticOwnerImpl_ambient_refines owner
    clearanceLe := strengthenQuadraticOwnerImpl_clearance_le owner
    directClearanceLe :=
      strengthenQuadraticOwnerImpl_direct_clearance_le owner
    clearanceEqMax :=
      strengthenQuadraticOwnerImpl_clearance_eq_max owner
    ambientClearanceEq :=
      strengthenQuadraticOwnerImpl_ambient_clearance_eq owner
    ambientDominance :=
      strengthenQuadraticOwnerImpl_ambientClearanceDominance owner }

/-- Strengthen exact side clearances when all four determinant checks pass,
and otherwise retain the input owner. -/
def strengthenQuadraticOwner {parameter : Gaussian}
    (owner : Owner parameter) : Owner parameter :=
  (certifiedStrengthening owner).value

theorem strengthenQuadraticOwner_initial_box {parameter : Gaussian}
    (owner : Owner parameter) :
    (strengthenQuadraticOwner owner).track.initial.box =
      owner.track.initial.box := by
  exact (certifiedStrengthening owner).initialBox

theorem strengthenQuadraticOwner_ambient_refines {parameter : Gaussian}
    (owner : Owner parameter) :
    (strengthenQuadraticOwner owner).ambient.Refines owner.ambient :=
  (certifiedStrengthening owner).ambientRefines

/-- The finite quadratic Horner budget survives same-box strengthening.  A
successful strengthening replaces the ambient by the displayed inner box;
all other branches retain the old ambient. -/
theorem strengthenQuadraticOwner_quadraticAmbientBudget
    {parameter : Gaussian} (owner : Owner parameter)
    (budget : QuadraticAmbientBudget owner) :
    QuadraticAmbientBudget (strengthenQuadraticOwner owner) := by
  have ambientRefines := strengthenQuadraticOwner_ambient_refines owner
  have verticalRefines : RFAP.PathClearance.Interval.Refines
      (RFAP.BoxClearance.verticalInterval
        (strengthenQuadraticOwner owner).ambient)
      (RFAP.BoxClearance.verticalInterval owner.ambient) :=
    ⟨ambientRefines.2.2.1, ambientRefines.2.2.2⟩
  have horizontalRefines : RFAP.PathClearance.Interval.Refines
      (RFAP.BoxClearance.horizontalInterval
        (strengthenQuadraticOwner owner).ambient)
      (RFAP.BoxClearance.horizontalInterval owner.ambient) :=
    ⟨ambientRefines.1, ambientRefines.2.1⟩
  refine
    { parameterNormSqLe := budget.parameterNormSqLe
      verticalIntervalSqLe :=
        (RFAP.PathClearance.Interval.squareBound_le_of_refines
          verticalRefines).trans budget.verticalIntervalSqLe
      horizontalIntervalSqLe :=
        (RFAP.PathClearance.Interval.squareBound_le_of_refines
          horizontalRefines).trans budget.horizontalIntervalSqLe
      leftNonzero := ?_
      rightNonzero := ?_
      bottomNonzero := ?_
      topNonzero := ?_
      leftSqLe := ?_
      rightSqLe := ?_
      bottomSqLe := ?_
      topSqLe := ?_ }
  · rw [strengthenQuadraticOwner_initial_box]
    exact budget.leftNonzero
  · rw [strengthenQuadraticOwner_initial_box]
    exact budget.rightNonzero
  · rw [strengthenQuadraticOwner_initial_box]
    exact budget.bottomNonzero
  · rw [strengthenQuadraticOwner_initial_box]
    exact budget.topNonzero
  · rw [strengthenQuadraticOwner_initial_box]
    exact budget.leftSqLe
  · rw [strengthenQuadraticOwner_initial_box]
    exact budget.rightSqLe
  · rw [strengthenQuadraticOwner_initial_box]
    exact budget.bottomSqLe
  · rw [strengthenQuadraticOwner_initial_box]
    exact budget.topSqLe

theorem strengthenQuadraticOwner_clearance_le
    {parameter : Gaussian} (owner : Owner parameter) :
    owner.track.initial.clearance.bound ≤
      (strengthenQuadraticOwner owner).track.initial.clearance.bound := by
  exact (certifiedStrengthening owner).clearanceLe

/-- Same-box strengthening preserves boundary-to-ambient dominance on every
executable branch. -/
theorem strengthenQuadraticOwner_ambientClearanceDominance_of
    {parameter : Gaussian} (owner : Owner parameter)
    (dominance : AmbientClearanceDominance owner) :
    AmbientClearanceDominance (strengthenQuadraticOwner owner) :=
  (certifiedStrengthening owner).ambientDominance dominance

/-- The exact four-side resultant clearance is available through the opaque
strengthening interface.  This avoids reevaluating the strengthening
implementation merely to use its quantitative improvement. -/
theorem directBoundaryClearance_le_strengthenQuadraticOwner
    {parameter : Gaussian} (owner : Owner parameter)
    (leftNonzero :
      CCL.Riemann.SquareRootContinuationChain.Owner.verticalDeterminant
        parameter owner.track.initial.box.xLower ≠ 0)
    (rightNonzero :
      CCL.Riemann.SquareRootContinuationChain.Owner.verticalDeterminant
        parameter owner.track.initial.box.xUpper ≠ 0)
    (bottomNonzero :
      CCL.Riemann.SquareRootContinuationChain.Owner.horizontalDeterminant
        parameter owner.track.initial.box.yLower ≠ 0)
    (topNonzero :
      CCL.Riemann.SquareRootContinuationChain.Owner.horizontalDeterminant
        parameter owner.track.initial.box.yUpper ≠ 0) :
    (directBoundaryClearance parameter owner.track.initial.box leftNonzero
        rightNonzero bottomNonzero topNonzero).bound ≤
      (strengthenQuadraticOwner owner).track.initial.clearance.bound := by
  exact (certifiedStrengthening owner).directClearanceLe leftNonzero
    rightNonzero bottomNonzero topNonzero

/-- Exact rational clearance exposed by the opaque strengthening cache. -/
theorem strengthenQuadraticOwner_clearance_eq_max
    {parameter : Gaussian} (owner : Owner parameter)
    (leftNonzero :
      CCL.Riemann.SquareRootContinuationChain.Owner.verticalDeterminant
        parameter owner.track.initial.box.xLower ≠ 0)
    (rightNonzero :
      CCL.Riemann.SquareRootContinuationChain.Owner.verticalDeterminant
        parameter owner.track.initial.box.xUpper ≠ 0)
    (bottomNonzero :
      CCL.Riemann.SquareRootContinuationChain.Owner.horizontalDeterminant
        parameter owner.track.initial.box.yLower ≠ 0)
    (topNonzero :
      CCL.Riemann.SquareRootContinuationChain.Owner.horizontalDeterminant
        parameter owner.track.initial.box.yUpper ≠ 0) :
    (strengthenQuadraticOwner owner).track.initial.clearance.bound =
      max owner.track.initial.clearance.bound
        (directBoundaryClearance parameter owner.track.initial.box leftNonzero
          rightNonzero bottomNonzero topNonzero).bound := by
  exact (certifiedStrengthening owner).clearanceEqMax leftNonzero rightNonzero
    bottomNonzero topNonzero

/-- A successful same-box strengthening caches its improved boundary
clearance on all four ambient sides as well.  Subsequent transport proofs can
therefore carry one numerical reserve instead of reopening the strengthening
implementation. -/
theorem strengthenQuadraticOwner_ambient_clearance_eq
    {parameter : Gaussian} (owner : Owner parameter)
    (leftNonzero :
      CCL.Riemann.SquareRootContinuationChain.Owner.verticalDeterminant
        parameter owner.track.initial.box.xLower ≠ 0)
    (rightNonzero :
      CCL.Riemann.SquareRootContinuationChain.Owner.verticalDeterminant
        parameter owner.track.initial.box.xUpper ≠ 0)
    (bottomNonzero :
      CCL.Riemann.SquareRootContinuationChain.Owner.horizontalDeterminant
        parameter owner.track.initial.box.yLower ≠ 0)
    (topNonzero :
      CCL.Riemann.SquareRootContinuationChain.Owner.horizontalDeterminant
        parameter owner.track.initial.box.yUpper ≠ 0) :
    let strengthened := strengthenQuadraticOwner owner
    strengthened.track.initial.ambientLeftClearance.bound =
        strengthened.track.initial.clearance.bound ∧
      strengthened.track.initial.ambientRightClearance.bound =
          strengthened.track.initial.clearance.bound ∧
        strengthened.track.initial.ambientBottomClearance.bound =
            strengthened.track.initial.clearance.bound ∧
          strengthened.track.initial.ambientTopClearance.bound =
            strengthened.track.initial.clearance.bound := by
  exact (certifiedStrengthening owner).ambientClearanceEq leftNonzero
    rightNonzero bottomNonzero topNonzero

/-- A successful four-resultant strengthening restores the finite
boundary-to-ambient dominance invariant, independently of the input owner's
ambient certificates. -/
theorem strengthenQuadraticOwner_ambientClearanceDominance
    {parameter : Gaussian} (owner : Owner parameter)
    (leftNonzero :
      CCL.Riemann.SquareRootContinuationChain.Owner.verticalDeterminant
        parameter owner.track.initial.box.xLower ≠ 0)
    (rightNonzero :
      CCL.Riemann.SquareRootContinuationChain.Owner.verticalDeterminant
        parameter owner.track.initial.box.xUpper ≠ 0)
    (bottomNonzero :
      CCL.Riemann.SquareRootContinuationChain.Owner.horizontalDeterminant
        parameter owner.track.initial.box.yLower ≠ 0)
    (topNonzero :
      CCL.Riemann.SquareRootContinuationChain.Owner.horizontalDeterminant
        parameter owner.track.initial.box.yUpper ≠ 0) :
    AmbientClearanceDominance (strengthenQuadraticOwner owner) := by
  rcases strengthenQuadraticOwner_ambient_clearance_eq owner leftNonzero
    rightNonzero bottomNonzero topNonzero with
    ⟨leftEq, rightEq, bottomEq, topEq⟩
  exact
    { left := le_of_eq leftEq.symm
      right := le_of_eq rightEq.symm
      bottom := le_of_eq bottomEq.symm
      top := le_of_eq topEq.symm }

attribute [irreducible] strengthenQuadraticOwner

end CCL.Riemann.ExactQuadraticOwnerClearance
