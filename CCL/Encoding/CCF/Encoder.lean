import mathlib.Tactic.QuotientFreeOmega
import mathlib.Tactic.QuotientFreeRing
import CCL.Encoding.CCF.Contraction

/-!
# Executable constructive coordinate-floor CCF encoder

The encoder groups at most three ordinary coordinate-floor clauses into one
well-founded recursive call.  Its measure is the natural squared norm of the
displayed uncancelled Gaussian denominator.
-/

namespace CCL.CCFEncoder

abbrev Coordinate := RFAP.ConstructiveFraction.Rational
abbrev Gaussian := RFAP.ConstructiveGaussian.Gaussian
abbrev GaussianInt := CCL.Integral.GaussianInt
abbrev Frac := CCL.Integral.Frac
abbrev Proj := CCL.Proj Gaussian
abbrev Mat2 := CCL.Mat2 Gaussian
abbrev IntegralProj := CCL.Proj GaussianInt
abbrev IntegralMat2 := CCL.Mat2 GaussianInt

open RFAP.ConstructiveGaussian.Gaussian
open CCL.Integral
open CCL.Integral.GaussianInt

/-- The coordinate-floor digit of an uncancelled fraction. -/
def digit (fraction : Frac) : GaussianInt :=
  CCL.CoordinateFloor.floor fraction.value

/-- The square residual `z - floor(z)`. -/
def residual (fraction : Frac) : Gaussian :=
  fraction.value - toGaussian (digit fraction)

/-- The uncancelled Gaussian-integer numerator of the residual. -/
def remainder (fraction : Frac) : GaussianInt :=
  fraction.num - digit fraction * fraction.den

theorem residual_sq (fraction : Frac) :
    CCL.CoordinateFloor.Sq (residual fraction) := by
  simpa only [residual, digit, CCL.CoordinateFloor.fract] using
    CCL.CoordinateFloor.fract_sq fraction.value

theorem remainder_toGaussian (fraction : Frac) :
    toGaussian (remainder fraction) =
      residual fraction * toGaussian fraction.den := by
  rw [remainder, toGaussian_sub, toGaussian_mul]
  simp only [residual, digit]
  rw [← fraction.value_mul_den]
  apply RFAP.ConstructiveGaussian.Gaussian.ext <;>
    simp only [RFAP.ConstructiveGaussian.Gaussian.sub_re,
      RFAP.ConstructiveGaussian.Gaussian.sub_im,
      RFAP.ConstructiveGaussian.Gaussian.mul_re,
      RFAP.ConstructiveGaussian.Gaussian.mul_im] <;>
    ring1

theorem residual_ne_zero {fraction : Frac}
    (remainderNonzero : remainder fraction ≠ 0) :
    residual fraction ≠ 0 := by
  intro residualZero
  have identity := remainder_toGaussian fraction
  rw [residualZero, RFAP.ConstructiveGaussian.Gaussian.zero_mul] at identity
  exact remainderNonzero
    (CCL.Integral.GaussianInt.toGaussian_eq_zero.mp identity)

/-- One nonterminal CCF transition, without cancellation. -/
def next (fraction : Frac) (remainderNonzero : remainder fraction ≠ 0) :
    Frac :=
  ⟨gammaInt * fraction.den, remainder fraction, remainderNonzero⟩

@[simp] theorem next_num (fraction : Frac)
    (remainderNonzero : remainder fraction ≠ 0) :
    (next fraction remainderNonzero).num = gammaInt * fraction.den := rfl

@[simp] theorem next_den (fraction : Frac)
    (remainderNonzero : remainder fraction ≠ 0) :
    (next fraction remainderNonzero).den = remainder fraction := rfl

/-- Exact semantic transition `z_next = gamma/(z-floor(z))`. -/
theorem next_value (fraction : Frac)
    (remainderNonzero : remainder fraction ≠ 0) :
    (next fraction remainderNonzero).value =
      gamma * (residual fraction)⁻¹ := by
  have remainderGaussianNonzero : toGaussian (remainder fraction) ≠ 0 := by
    intro gaussianZero
    exact remainderNonzero
      (CCL.Integral.GaussianInt.toGaussian_eq_zero.mp gaussianZero)
  apply RFAP.ConstructiveGaussian.Gaussian.mul_right_cancel_of_ne
    remainderGaussianNonzero
  calc
    (next fraction remainderNonzero).value * toGaussian (remainder fraction) =
        toGaussian (gammaInt * fraction.den) :=
      (next fraction remainderNonzero).value_mul_den
    _ = gamma * toGaussian fraction.den := by
      rw [toGaussian_mul, toGaussian_gammaInt]
    _ = (gamma * (residual fraction)⁻¹) *
          toGaussian (remainder fraction) := by
      rw [remainder_toGaussian,
        RFAP.ConstructiveGaussian.Gaussian.mul_assoc,
        ← RFAP.ConstructiveGaussian.Gaussian.mul_assoc
          (residual fraction)⁻¹,
        RFAP.ConstructiveGaussian.Gaussian.inv_eq,
        RFAP.ConstructiveGaussian.Gaussian.inv_mul _
          (residual_ne_zero remainderNonzero),
        RFAP.ConstructiveGaussian.Gaussian.one_mul]

/-- Successive residuals are exactly iterates of the square return map. -/
theorem residual_next (fraction : Frac)
    (remainderNonzero : remainder fraction ≠ 0) :
    residual (next fraction remainderNonzero) =
      CCL.CoordinateFloor.step (residual fraction) := by
  rw [residual, digit, next_value]
  rfl

/-- Exact natural-norm relation for the next uncancelled denominator. -/
theorem next_den_norm (fraction : Frac)
    (remainderNonzero : remainder fraction ≠ 0) :
    (normNat (next fraction remainderNonzero).den : Coordinate) =
      normSq (residual fraction) * (normNat fraction.den : Coordinate) := by
  rw [next_den, ← normSq_toGaussian, remainder_toGaussian, normSq_mul,
    normSq_toGaussian]

/-- Three nonterminal clauses strictly decrease the original uncancelled
denominator norm. -/
theorem three_den_descent (fraction : Frac)
    (firstNonzero : remainder fraction ≠ 0)
    (secondNonzero : remainder (next fraction firstNonzero) ≠ 0)
    (thirdNonzero :
      remainder (next (next fraction firstNonzero) secondNonzero) ≠ 0) :
    normNat
        (next (next (next fraction firstNonzero) secondNonzero)
          thirdNonzero).den <
      normNat fraction.den := by
  let first := next fraction firstNonzero
  let second := next first secondNonzero
  let third := next second thirdNonzero
  let u := residual fraction
  have uNonzero : u ≠ 0 := residual_ne_zero firstNonzero
  have firstResidual :
      residual first = CCL.CoordinateFloor.step u := by
    dsimp only [first, u]
    exact residual_next fraction firstNonzero
  have secondResidualNonzero :
      CCL.CoordinateFloor.step u ≠ 0 := by
    rw [← firstResidual]
    exact residual_ne_zero secondNonzero
  have secondResidual :
      residual second = CCL.CoordinateFloor.step
        (CCL.CoordinateFloor.step u) := by
    rw [residual_next first secondNonzero, firstResidual]
  have contraction :=
    CCL.CCFContraction.three_step_contraction
      u uNonzero (residual_sq fraction) secondResidualNonzero
  have firstNorm := next_den_norm fraction firstNonzero
  have secondNorm := next_den_norm first secondNonzero
  have thirdNorm := next_den_norm second thirdNonzero
  have normIdentity : (normNat third.den : Coordinate) =
      normSq (u * CCL.CoordinateFloor.step u *
        CCL.CoordinateFloor.step
          (CCL.CoordinateFloor.step u)) *
        (normNat fraction.den : Coordinate) := by
    calc
      (normNat third.den : Coordinate) =
          normSq (residual second) * (normNat second.den : Coordinate) :=
        thirdNorm
      _ = normSq (residual second) *
          (normSq (residual first) * (normNat first.den : Coordinate)) := by
        rw [secondNorm]
      _ = normSq (residual second) *
          (normSq (residual first) *
            (normSq u * (normNat fraction.den : Coordinate))) := by
        rw [firstNorm]
      _ = normSq (u * residual first * residual second) *
          (normNat fraction.den : Coordinate) := by
        rw [normSq_mul, normSq_mul]
        ring1
      _ = normSq (u * CCL.CoordinateFloor.step u *
          CCL.CoordinateFloor.step
            (CCL.CoordinateFloor.step u)) *
          (normNat fraction.den : Coordinate) := by
        rw [firstResidual, secondResidual]
  have denominatorPositive :
      (0 : Coordinate) < (normNat fraction.den : Coordinate) :=
    RFAP.ConstructiveFraction.natCast_pos_direct
      (normNat_pos fraction.den_ne)
  have scaled := RFAP.ConstructiveFraction.mul_lt_mul_of_pos_right_direct
    contraction denominatorPositive
  have castDescent : (normNat third.den : Coordinate) <
      (normNat fraction.den : Coordinate) := by
    rw [normIdentity]
    simpa only [RFAP.ConstructiveFraction.one_mul] using scaled
  exact (RFAP.ConstructiveFraction.natCast_lt_iff_direct).1 castDescent

/-- The integral decoder matrix `A(t,gamma)` for one emitted CCF digit. -/
def digitMatrix (t : GaussianInt) : IntegralMat2 := CCL.Mat2.cf t gammaInt

/-- Coordinatewise embedding of an integral projective pair. -/
def mapProj (point : IntegralProj) : Proj :=
  ⟨toGaussian point.p, toGaussian point.q⟩

/-- Coordinatewise embedding of an integral decoder matrix. -/
def mapMat (matrix : IntegralMat2) : Mat2 :=
  ⟨toGaussian matrix.a, toGaussian matrix.b,
    toGaussian matrix.c, toGaussian matrix.d⟩

@[simp] theorem mapProj_omega :
    mapProj (CCL.Proj.omega : IntegralProj) =
      (CCL.Proj.omega : Proj) := rfl

@[simp] theorem mapProj_act (matrix : IntegralMat2) (point : IntegralProj) :
    mapProj (CCL.Mat2.act matrix point) =
      CCL.Mat2.act (mapMat matrix) (mapProj point) := by
  ext <;> simp only [mapProj, mapMat, CCL.Mat2.act,
    toGaussian_add, toGaussian_mul]

theorem mapProj_equivalent {left right : IntegralProj}
    (equivalent : CCL.Proj.Equivalent left right) :
    CCL.Proj.Equivalent (mapProj left) (mapProj right) := by
  dsimp only [CCL.Proj.Equivalent, mapProj] at equivalent ⊢
  simpa only [toGaussian_mul] using congrArg toGaussian equivalent

theorem map_digitMatrix (t : GaussianInt) :
    mapMat (digitMatrix t) = CCL.Mat2.cf (toGaussian t) gamma := by
  ext <;> simp only [mapMat, digitMatrix, CCL.Mat2.cf,
    toGaussian_gammaInt, toGaussian_one, toGaussian_zero]

/-- A finite digit list, its decoder product in emission order, and exact
projective reconstruction of the input fraction. -/
structure Encoding (fraction : Frac) where
  digits : List GaussianInt
  matrix : IntegralMat2
  reconstruct :
    (CCL.Mat2.act matrix
      (CCL.Proj.omega : IntegralProj)).Equivalent
      ⟨fraction.num, fraction.den⟩

private def terminal (fraction : Frac)
    (remainderZero : remainder fraction = 0) : Encoding fraction := by
  have numeratorIdentity : fraction.num = digit fraction * fraction.den := by
    rw [remainder] at remainderZero
    exact sub_eq_zero.mp remainderZero
  refine ⟨[digit fraction], digitMatrix (digit fraction), ?_⟩
  rw [numeratorIdentity]
  dsimp only [digitMatrix, CCL.Proj.Equivalent, CCL.Mat2.act,
    CCL.Mat2.cf, CCL.Proj.omega]
  ring1

private theorem digit_step_reconstruct (fraction : Frac)
    (remainderNonzero : remainder fraction ≠ 0) :
    (CCL.Mat2.act (digitMatrix (digit fraction))
      ⟨(next fraction remainderNonzero).num,
        (next fraction remainderNonzero).den⟩).Equivalent
      ⟨fraction.num, fraction.den⟩ := by
  dsimp only [digitMatrix, CCL.Proj.Equivalent, CCL.Mat2.act,
    CCL.Mat2.cf, next, remainder]
  apply CCL.Integral.GaussianInt.ext <;>
    simp only [CCL.Integral.GaussianInt.add_re,
      CCL.Integral.GaussianInt.add_im,
      CCL.Integral.GaussianInt.mul_re,
      CCL.Integral.GaussianInt.mul_im,
      CCL.Integral.GaussianInt.sub_re,
      CCL.Integral.GaussianInt.sub_im,
      CCL.Integral.GaussianInt.one_re,
      CCL.Integral.GaussianInt.one_im,
      CCL.Integral.GaussianInt.zero_re,
      CCL.Integral.GaussianInt.zero_im,
      CCL.Integral.GaussianInt.gammaInt] <;>
    ring1

private theorem digit_step_den_ne (fraction : Frac)
    (remainderNonzero : remainder fraction ≠ 0) :
    (CCL.Mat2.act (digitMatrix (digit fraction))
      ⟨(next fraction remainderNonzero).num,
        (next fraction remainderNonzero).den⟩).q ≠ 0 := by
  have denominatorIdentity :
      (CCL.Mat2.act (digitMatrix (digit fraction))
        ⟨(next fraction remainderNonzero).num,
          (next fraction remainderNonzero).den⟩).q =
        gammaInt * fraction.den := by
    dsimp only [digitMatrix, CCL.Mat2.act, CCL.Mat2.cf, next]
    ring1
  rw [denominatorIdentity]
  exact CCL.Integral.GaussianInt.mul_ne_zero
    (show gammaInt ≠ 0 by decide) fraction.den_ne

/-- Prepend one nonterminal digit and its inverse-branch matrix. -/
private def prepend (fraction : Frac)
    (remainderNonzero : remainder fraction ≠ 0)
    (tail : Encoding (next fraction remainderNonzero)) : Encoding fraction :=
  let matrix := CCL.Mat2.mul (digitMatrix (digit fraction)) tail.matrix
  ⟨digit fraction :: tail.digits, matrix, by
    dsimp only [matrix]
    rw [CCL.Mat2.act_mul]
    have acted := CCL.Mat2.act_respects_equivalent
      (digitMatrix (digit fraction)) tail.reconstruct
    exact CCL.Integral.GaussianInt.equivalent_trans_of_mid_q
      acted (digit_step_reconstruct fraction remainderNonzero)
      (digit_step_den_ne fraction remainderNonzero)⟩

/-- The finite coordinate-floor encoder, using a three-clause macro-step for
each well-founded recursive call. -/
def encodeResult (fraction : Frac) : Encoding fraction :=
  if firstZero : remainder fraction = 0 then
    terminal fraction firstZero
  else
    let first := next fraction firstZero
    if secondZero : remainder first = 0 then
      prepend fraction firstZero (terminal first secondZero)
    else
      let second := next first secondZero
      if thirdZero : remainder second = 0 then
        prepend fraction firstZero
          (prepend first secondZero (terminal second thirdZero))
      else
        let third := next second thirdZero
        prepend fraction firstZero
          (prepend first secondZero
            (prepend second thirdZero (encodeResult third)))
termination_by normNat fraction.den
decreasing_by exact three_den_descent fraction firstZero secondZero thirdZero

/-- The finite coordinate-floor digit list. -/
def encode (fraction : Frac) : List GaussianInt :=
  (encodeResult fraction).digits

/-- Integral projective reconstruction of every finite CCF encoding. -/
theorem encode_reconstruct_pair (fraction : Frac) :
    (CCL.Mat2.act (encodeResult fraction).matrix
      (CCL.Proj.omega : IntegralProj)).Equivalent
      ⟨fraction.num, fraction.den⟩ :=
  (encodeResult fraction).reconstruct

/-- Exact affine reconstruction in constructive Gaussian coordinates. -/
theorem encode_reconstruct (fraction : Frac) :
    (CCL.Mat2.act (mapMat (encodeResult fraction).matrix)
      (CCL.Proj.omega : Proj)).Equivalent
      (CCL.Proj.affine fraction.value) := by
  have mapped := mapProj_equivalent (encodeResult fraction).reconstruct
  rw [mapProj_act, mapProj_omega] at mapped
  dsimp only [CCL.Proj.Equivalent, mapProj, CCL.Proj.affine] at mapped ⊢
  rw [RFAP.ConstructiveGaussian.Gaussian.mul_one]
  apply RFAP.ConstructiveGaussian.Gaussian.mul_right_cancel_of_ne
    fraction.den_toGaussian_ne
  calc
    (CCL.Mat2.act (mapMat (encodeResult fraction).matrix)
        (CCL.Proj.omega : Proj)).p * toGaussian fraction.den =
        toGaussian fraction.num *
          (CCL.Mat2.act (mapMat (encodeResult fraction).matrix)
            (CCL.Proj.omega : Proj)).q := mapped
    _ = (fraction.value * toGaussian fraction.den) *
          (CCL.Mat2.act (mapMat (encodeResult fraction).matrix)
            (CCL.Proj.omega : Proj)).q := by rw [fraction.value_mul_den]
    _ = (fraction.value *
          (CCL.Mat2.act (mapMat (encodeResult fraction).matrix)
            (CCL.Proj.omega : Proj)).q) * toGaussian fraction.den := by
      rw [RFAP.ConstructiveGaussian.Gaussian.mul_assoc,
        RFAP.ConstructiveGaussian.Gaussian.mul_comm
          (toGaussian fraction.den),
        ← RFAP.ConstructiveGaussian.Gaussian.mul_assoc]

end CCL.CCFEncoder
