import mathlib.Tactic.QuotientFreeOmega
import mathlib.Tactic.QuotientFreeRing
import CCL.Measure.PrefixSquaredStability
import FiniteMeasure.VarianceLp

/-!
# A nonconstant root-free CCL probe

Squared chordal distance to the distinguished projective point `omega` is an
exact rational observable on every valid homogeneous point.  Its output
separation is not naturally linear in squared chordal distance, but its
*squared* output separation is.  This supplies a concrete nonconstant probe
for the root-free L2 prefix-stability interface.
-/

namespace CCL.FiniteMeasure

open RFAP.ConstructiveGaussian.Gaussian

/-- Exact rational squared chordal distance to the projective point at
infinity. -/
def chordalOmegaProbe (point : Proj) : Coordinate :=
  CCL.Chordal.chordalSq point (CCL.Proj.omega : Proj)

theorem chordalOmegaProbe_nonnegative (point : Proj) :
    0 ≤ chordalOmegaProbe point :=
  CCL.Chordal.chordalSq_nonneg point (CCL.Proj.omega : Proj)

theorem chordalOmegaProbe_le_one {point : Proj}
    (valid : CCL.Chordal.Proj.HasNonzeroCoordinate point) :
    chordalOmegaProbe point ≤ 1 :=
  CCL.Chordal.chordalSq_le_one valid
    CCL.Chordal.Proj.omega_hasNonzeroCoordinate

/-- Every finite law of valid projective points has distance-to-`omega`
variance at most one. -/
theorem chordalOmegaProbe_variance_le_one {index : Type}
    (distribution : _root_.FiniteMeasure.Distribution index)
    (points : index → Proj)
    (valid : ∀ atom, atom ∈ distribution.atoms →
      CCL.Chordal.Proj.HasNonzeroCoordinate (points atom.item)) :
    distribution.variance (fun item => chordalOmegaProbe (points item)) ≤ 1 :=
  calc
    distribution.variance (fun item => chordalOmegaProbe (points item)) ≤
        distribution.poweredL2
          (fun item => chordalOmegaProbe (points item)) :=
      distribution.variance_le_poweredL2 _
    _ ≤ distribution.expectation (fun _ => 1) := by
      apply distribution.expectation_mono
      intro atom member
      have squareLe := RFAP.ConstructiveFraction.pow_le_pow_direct
        (chordalOmegaProbe_nonnegative (points atom.item))
        (chordalOmegaProbe_le_one (valid atom member)) 2
      simpa only [one_pow] using squareLe
    _ = 1 := distribution.expectation_constant 1

private theorem chordalSq_omega_eq_weight (point : Proj) :
    chordalOmegaProbe point =
      normSq point.q / CCL.Chordal.Proj.weight point := by
  unfold chordalOmegaProbe
  rw [CCL.Chordal.chordalSq_eq_cross]
  simp only [CCL.Chordal.Proj.cross, CCL.Proj.omega,
    RFAP.ConstructiveGaussian.Gaussian.mul_zero,
    RFAP.ConstructiveGaussian.Gaussian.one_mul,
    RFAP.ConstructiveGaussian.Gaussian.zero_sub,
    normSq_neg, CCL.Chordal.Proj.weight, normSq_one, normSq_zero]
  congr 1
  ring1

private theorem normSq_difference_sq_le_two_mul
    (left right : RFAP.ConstructiveGaussian.Gaussian) :
    (normSq left - normSq right) ^ 2 ≤
      2 * normSq (left - right) * (normSq left + normSq right) := by
  let difference := left - right
  let total := left + right
  let dot := difference.re * total.re + difference.im * total.im
  have dotIdentity : dot = normSq left - normSq right := by
    dsimp only [dot, difference, total, normSq]
    simp only [sub_re, sub_im, add_re, add_im]
    ring1
  have cauchy : dot ^ 2 ≤ normSq difference * normSq total := by
    apply RFAP.ConstructiveFraction.le_of_sub_nonneg_direct
    calc
      0 ≤
          (difference.re * total.im - difference.im * total.re) ^ 2 :=
        RFAP.ConstructiveFraction.sq_nonneg_direct _
      _ = normSq difference * normSq total - dot ^ 2 := by
        dsimp only [normSq, dot]
        ring1
  calc
    (normSq left - normSq right) ^ 2 = dot ^ 2 := by rw [dotIdentity]
    _ ≤ normSq difference * normSq total := cauchy
    _ ≤ normSq difference *
        (2 * (normSq left + normSq right)) :=
      RFAP.ConstructiveFraction.mul_le_mul_of_nonneg_left_direct
        (normSq_add_le_two left right) (normSq_nonneg difference)
    _ = 2 * normSq (left - right) *
        (normSq left + normSq right) := by
      dsimp only [difference]
      ring1

private theorem crossProductNorms_le_weightProduct (left right : Proj) :
    normSq (left.q * right.p) + normSq (right.q * left.p) ≤
      CCL.Chordal.Proj.weight left * CCL.Chordal.Proj.weight right := by
  rw [normSq_mul, normSq_mul]
  apply RFAP.ConstructiveFraction.le_of_sub_nonneg_direct
  calc
    0 ≤ normSq left.p * normSq right.p +
        normSq left.q * normSq right.q :=
      add_nonneg
        (RFAP.ConstructiveFraction.mul_nonneg_direct
          (normSq_nonneg left.p) (normSq_nonneg right.p))
        (RFAP.ConstructiveFraction.mul_nonneg_direct
          (normSq_nonneg left.q) (normSq_nonneg right.q))
    _ = CCL.Chordal.Proj.weight left *
          CCL.Chordal.Proj.weight right -
        (normSq left.q * normSq right.p +
          normSq right.q * normSq left.p) := by
      dsimp only [CCL.Chordal.Proj.weight]
      ring1

/-- Squared output separation of the nonconstant `omega`-distance probe is
at most twice the squared chordal separation of its valid inputs. -/
theorem chordalOmegaProbe_squaredSensitive :
    SquaredProbeSensitive chordalOmegaProbe 2 := by
  intro left right leftValid rightValid
  let leftWeight := CCL.Chordal.Proj.weight left
  let rightWeight := CCL.Chordal.Proj.weight right
  let denominator := leftWeight * rightWeight
  let first := left.q * right.p
  let second := right.q * left.p
  have leftWeightPositive : 0 < leftWeight :=
    CCL.Chordal.Proj.weight_pos leftValid
  have rightWeightPositive : 0 < rightWeight :=
    CCL.Chordal.Proj.weight_pos rightValid
  have denominatorPositive : 0 < denominator :=
    RFAP.ConstructiveFraction.mul_pos_direct leftWeightPositive
      rightWeightPositive
  have probeDifference : chordalOmegaProbe left - chordalOmegaProbe right =
      (normSq first - normSq second) / denominator := by
    rw [chordalSq_omega_eq_weight, chordalSq_omega_eq_weight]
    change normSq left.q / leftWeight - normSq right.q / rightWeight =
      (normSq first - normSq second) / (leftWeight * rightWeight)
    calc
      normSq left.q / leftWeight - normSq right.q / rightWeight =
          (normSq left.q * rightWeight -
            normSq right.q * leftWeight) /
              (leftWeight * rightWeight) :=
        RFAP.ConstructiveFraction.div_sub_div_direct
          (normSq left.q) leftWeight (normSq right.q) rightWeight
          leftWeightPositive.ne' rightWeightPositive.ne'
      _ = (normSq first - normSq second) /
          (leftWeight * rightWeight) := by
        apply congrArg (fun numerator =>
          numerator / (leftWeight * rightWeight))
        dsimp only [first, second, leftWeight, rightWeight,
          CCL.Chordal.Proj.weight]
        rw [normSq_mul, normSq_mul]
        ring1
  have crossIdentity : first - second =
      -(CCL.Chordal.Proj.cross left right) := by
    apply RFAP.ConstructiveGaussian.Gaussian.ext <;>
      dsimp only [first, second, CCL.Chordal.Proj.cross] <;>
      simp only [sub_re, sub_im, mul_re, mul_im, neg_re, neg_im] <;>
      ring1
  have numeratorBound :
      (normSq first - normSq second) ^ 2 ≤
        2 * normSq (CCL.Chordal.Proj.cross left right) * denominator := by
    have differenceBound := normSq_difference_sq_le_two_mul first second
    rw [crossIdentity, normSq_neg] at differenceBound
    calc
      (normSq first - normSq second) ^ 2 ≤
          2 * normSq (CCL.Chordal.Proj.cross left right) *
            (normSq first + normSq second) := differenceBound
      _ ≤ 2 * normSq (CCL.Chordal.Proj.cross left right) *
          denominator :=
        RFAP.ConstructiveFraction.mul_le_mul_of_nonneg_left_direct
          (crossProductNorms_le_weightProduct left right)
          (RFAP.ConstructiveFraction.mul_nonneg_direct (by decide)
            (normSq_nonneg (CCL.Chordal.Proj.cross left right)))
  have quotientSquare :
      ((normSq first - normSq second) / denominator) ^ 2 =
        (normSq first - normSq second) ^ 2 / denominator ^ 2 := by
    calc
      ((normSq first - normSq second) / denominator) ^ 2 =
          ((normSq first - normSq second) / denominator) *
            ((normSq first - normSq second) / denominator) := by ring1
      _ = ((normSq first - normSq second) *
          (normSq first - normSq second)) /
            (denominator * denominator) :=
        RFAP.ConstructiveFraction.div_mul_div_direct _ _ _ _
      _ = (normSq first - normSq second) ^ 2 /
          (denominator * denominator) := by
        apply congrArg (fun numerator =>
          numerator / (denominator * denominator))
        ring1
      _ = (normSq first - normSq second) ^ 2 /
          denominator ^ 2 := by
        apply congrArg (fun divisor =>
          (normSq first - normSq second) ^ 2 / divisor)
        ring1
  rw [_root_.FiniteMeasure.rationalSeparation_sq, probeDifference,
    quotientSquare, CCL.Chordal.chordalSq_eq_cross]
  have denominatorSquarePositive : 0 < denominator ^ 2 :=
    RFAP.ConstructiveFraction.pow_pos_direct denominatorPositive 2
  apply (RFAP.ConstructiveFraction.div_le_iff_pos
    denominatorSquarePositive).2
  calc
    (normSq first - normSq second) ^ 2 ≤
        2 * normSq (CCL.Chordal.Proj.cross left right) * denominator :=
      numeratorBound
    _ = (2 *
        (normSq (CCL.Chordal.Proj.cross left right) / denominator)) *
          denominator ^ 2 := by
      rw [pow_two]
      have cancel := RFAP.ConstructiveFraction.div_mul_cancel_of_ne
        (normSq (CCL.Chordal.Proj.cross left right)) denominator
        denominatorPositive.ne'
      have replaceCancel := congrArg (fun value =>
        2 * value * denominator) cancel
      calc
        2 * normSq (CCL.Chordal.Proj.cross left right) * denominator =
            2 * ((normSq (CCL.Chordal.Proj.cross left right) /
              denominator) * denominator) * denominator :=
          replaceCancel.symm
        _ = (2 *
            (normSq (CCL.Chordal.Proj.cross left right) / denominator)) *
              (denominator * denominator) := by ring1

end CCL.FiniteMeasure
