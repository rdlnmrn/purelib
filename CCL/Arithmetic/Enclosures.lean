import mathlib.Tactic.QuotientFreeRing
import CCL.Encoding.TerminalPadding

/-!
# Finite squared-error enclosures for constructive CCL arithmetic

The standalone CCL word remains a list of bits.  Arithmetic uses a proof
sidecar: a rational centre and a rational squared Euclidean error.  The
operations below transport these finite certificates directly.  They do not
name completed limits or collections of compatible points.
-/

namespace CCL.ArithmeticEnclosures

abbrev Coordinate := RFAP.ConstructiveFraction.Rational
abbrev Gaussian := RFAP.ConstructiveGaussian.Gaussian

open RFAP.ConstructiveGaussian.Gaussian

/-- A finite rational centre with a nonnegative squared-error allowance. -/
structure Ball where
  center : Gaussian
  radiusSq : Coordinate
  radiusSq_nonneg : 0 ≤ radiusSq

namespace Ball

private theorem gaussian_div_sub_div_direct
    (a b c d : Gaussian) (cNonzero : c ≠ 0) (dNonzero : d ≠ 0) :
    a / c - b / d = (a * d - b * c) / (c * d) := by
  have productNonzero := mul_ne_zero_direct cNonzero dNonzero
  apply mul_right_cancel_of_ne productNonzero
  calc
    (a / c - b / d) * (c * d) =
        (a / c * c) * d - (b / d * d) * c := by
      apply RFAP.ConstructiveGaussian.Gaussian.ext <;>
        simp only [sub_re, sub_im, mul_re, mul_im] <;> ring1
    _ = a * d - b * c := by
      rw [RFAP.ExplicitField.div_mul_cancel a cNonzero,
        RFAP.ExplicitField.div_mul_cancel b dNonzero]
    _ = ((a * d - b * c) / (c * d)) * (c * d) :=
      (RFAP.ExplicitField.div_mul_cancel _ productNonzero).symm

def Contains (ball : Ball) (value : Gaussian) : Prop :=
  normSq (value - ball.center) ≤ ball.radiusSq

instance containsDecidable (ball : Ball) (value : Gaussian) :
    Decidable (ball.Contains value) := by
  unfold Contains
  infer_instance

theorem contains_center (ball : Ball) : ball.Contains ball.center := by
  unfold Contains
  rw [RFAP.ConstructiveGaussian.Gaussian.sub_self, normSq_zero]
  exact ball.radiusSq_nonneg

/-- Convert an existing rational box to a centre-plus-squared-error sidecar
using its fixed lower-left anchor. -/
def ofBox (box : RFAP.Boxes.Box) : Ball :=
  { center := box.anchor
    radiusSq := box.diagonalSq
    radiusSq_nonneg := box.diagonalSq_nonneg }

theorem contains_ofBox {box : RFAP.Boxes.Box} {value : Gaussian}
    (inside : box.Contains value) : (ofBox box).Contains value :=
  box.normSq_sub_anchor_le inside

def neg (ball : Ball) : Ball :=
  { center := -ball.center
    radiusSq := ball.radiusSq
    radiusSq_nonneg := ball.radiusSq_nonneg }

theorem contains_neg {ball : Ball} {value : Gaussian}
    (inside : ball.Contains value) : ball.neg.Contains (-value) := by
  unfold Contains at inside ⊢
  change normSq (-value - -ball.center) ≤ ball.radiusSq
  have difference : -value - -ball.center = -(value - ball.center) := by
    apply RFAP.ConstructiveGaussian.Gaussian.ext <;>
      simp only [sub_re, sub_im, neg_re, neg_im] <;> ring1
  rw [difference, normSq_neg]
  exact inside

/-- Addition requires no magnitude bound.  The factor two is the rational
square-root-free triangle estimate. -/
def add (left right : Ball) : Ball :=
  { center := left.center + right.center
    radiusSq := 2 * (left.radiusSq + right.radiusSq)
    radiusSq_nonneg :=
      RFAP.ConstructiveFraction.mul_nonneg_direct (by decide)
        (add_nonneg left.radiusSq_nonneg right.radiusSq_nonneg) }

theorem contains_add {left right : Ball} {x y : Gaussian}
    (xInside : left.Contains x) (yInside : right.Contains y) :
    (left.add right).Contains (x + y) := by
  have difference :
      x + y - (left.center + right.center) =
        (x - left.center) + (y - right.center) := by
    apply RFAP.ConstructiveGaussian.Gaussian.ext <;>
      simp only [sub_re, sub_im, add_re, add_im] <;> ring1
  unfold Contains add
  rw [difference]
  calc
    normSq ((x - left.center) + (y - right.center)) ≤
        2 * (normSq (x - left.center) + normSq (y - right.center)) :=
      normSq_add_le_two _ _
    _ ≤ 2 * (left.radiusSq + right.radiusSq) :=
      RFAP.ConstructiveFraction.mul_le_mul_of_nonneg_left_direct
        (add_le_add xInside yInside) (by decide)

def sub (left right : Ball) : Ball := left.add right.neg

theorem contains_sub {left right : Ball} {x y : Gaussian}
    (xInside : left.Contains x) (yInside : right.Contains y) :
    (left.sub right).Contains (x - y) := by
  have negInside := contains_neg yInside
  have sumInside := contains_add xInside negInside
  have valueIdentity : x + -y = x - y := by
    apply RFAP.ConstructiveGaussian.Gaussian.ext <;>
      simp only [sub_re, sub_im, add_re, add_im, neg_re, neg_im] <;> ring1
  simpa only [sub, valueIdentity] using sumInside

/-- Multiplication transports both first-order errors and their product. -/
def mul (left right : Ball) : Ball :=
  { center := left.center * right.center
    radiusSq :=
      4 * (left.radiusSq * normSq right.center +
        normSq left.center * right.radiusSq) +
      2 * (left.radiusSq * right.radiusSq)
    radiusSq_nonneg := by
      exact add_nonneg
        (RFAP.ConstructiveFraction.mul_nonneg_direct (by decide)
          (add_nonneg
            (RFAP.ConstructiveFraction.mul_nonneg_direct
              left.radiusSq_nonneg (normSq_nonneg right.center))
            (RFAP.ConstructiveFraction.mul_nonneg_direct
              (normSq_nonneg left.center) right.radiusSq_nonneg)))
        (RFAP.ConstructiveFraction.mul_nonneg_direct (by decide)
          (RFAP.ConstructiveFraction.mul_nonneg_direct
            left.radiusSq_nonneg right.radiusSq_nonneg)) }

theorem contains_mul {left right : Ball} {x y : Gaussian}
    (xInside : left.Contains x) (yInside : right.Contains y) :
    (left.mul right).Contains (x * y) := by
  let dx := x - left.center
  let dy := y - right.center
  have difference :
      x * y - left.center * right.center =
        (dx * right.center + left.center * dy) + dx * dy := by
    dsimp only [dx, dy]
    apply RFAP.ConstructiveGaussian.Gaussian.ext <;>
      simp only [sub_re, sub_im, add_re, add_im, mul_re, mul_im] <;> ring1
  have firstTerm :
      normSq (dx * right.center) ≤
        left.radiusSq * normSq right.center := by
    rw [normSq_mul]
    exact RFAP.ConstructiveFraction.mul_le_mul_of_nonneg_right_direct
      xInside (normSq_nonneg right.center)
  have secondTerm :
      normSq (left.center * dy) ≤
        normSq left.center * right.radiusSq := by
    rw [normSq_mul]
    exact RFAP.ConstructiveFraction.mul_le_mul_of_nonneg_left_direct
      yInside (normSq_nonneg left.center)
  have productTerm : normSq (dx * dy) ≤
      left.radiusSq * right.radiusSq := by
    rw [normSq_mul]
    have firstScaled :=
      RFAP.ConstructiveFraction.mul_le_mul_of_nonneg_right_direct
        xInside (normSq_nonneg dy)
    exact firstScaled.trans
      (RFAP.ConstructiveFraction.mul_le_mul_of_nonneg_left_direct
        yInside left.radiusSq_nonneg)
  unfold Contains mul
  rw [difference]
  calc
    normSq ((dx * right.center + left.center * dy) + dx * dy) ≤
        2 * (normSq (dx * right.center + left.center * dy) +
          normSq (dx * dy)) := normSq_add_le_two _ _
    _ ≤ 2 *
        (2 * (normSq (dx * right.center) + normSq (left.center * dy)) +
          normSq (dx * dy)) := by
      exact RFAP.ConstructiveFraction.mul_le_mul_of_nonneg_left_direct
        (add_le_add (normSq_add_le_two _ _) le_rfl) (by decide)
    _ ≤ 2 *
        (2 * (left.radiusSq * normSq right.center +
          normSq left.center * right.radiusSq) +
          left.radiusSq * right.radiusSq) := by
      apply RFAP.ConstructiveFraction.mul_le_mul_of_nonneg_left_direct
      · apply add_le_add
        · exact RFAP.ConstructiveFraction.mul_le_mul_of_nonneg_left_direct
            (add_le_add firstTerm secondTerm) (by decide)
        · exact productTerm
      · decide
    _ = 4 * (left.radiusSq * normSq right.center +
          normSq left.center * right.radiusSq) +
        2 * (left.radiusSq * right.radiusSq) := by ring1

/-- A finite apartness sidecar for a denominator enclosure. -/
structure Apart (ball : Ball) where
  lowerSq : Coordinate
  positive : 0 < lowerSq
  lower : ∀ {value : Gaussian}, ball.Contains value →
    lowerSq ≤ normSq value

namespace Apart

theorem center_nonzero {ball : Ball} (apart : Apart ball) :
    ball.center ≠ 0 := by
  intro centerZero
  have lower := apart.lower ball.contains_center
  rw [centerZero, normSq_zero] at lower
  exact (not_le_of_gt apart.positive) lower

end Apart

/-- Division enclosure.  The denominator apartness certificate is explicit;
without it division is intentionally not a total arithmetic operation. -/
def div (numerator denominator : Ball) (apart : Apart denominator) : Ball :=
  let denominatorCenterNorm := normSq denominator.center
  { center := numerator.center / denominator.center
    radiusSq :=
      (2 * (numerator.radiusSq * denominatorCenterNorm +
        normSq numerator.center * denominator.radiusSq)) /
      (apart.lowerSq * denominatorCenterNorm)
    radiusSq_nonneg :=
      RFAP.ConstructiveFraction.div_nonneg_direct
        (RFAP.ConstructiveFraction.mul_nonneg_direct (by decide)
          (add_nonneg
            (RFAP.ConstructiveFraction.mul_nonneg_direct
              numerator.radiusSq_nonneg (normSq_nonneg denominator.center))
            (RFAP.ConstructiveFraction.mul_nonneg_direct
              (normSq_nonneg numerator.center)
              denominator.radiusSq_nonneg)))
        (RFAP.ConstructiveFraction.mul_nonneg_direct apart.positive.le
          (normSq_nonneg denominator.center)) }

theorem contains_div {numerator denominator : Ball}
    (apart : Apart denominator) {x y : Gaussian}
    (xInside : numerator.Contains x) (yInside : denominator.Contains y) :
    (numerator.div denominator apart).Contains (x / y) := by
  have yNormPositive := apart.positive.trans_le (apart.lower yInside)
  have yNonzero : y ≠ 0 := fun zero => by
    rw [zero, normSq_zero] at yNormPositive
    exact (lt_irrefl _ yNormPositive).elim
  have centerNonzero := apart.center_nonzero
  let denominatorCenterNorm := normSq denominator.center
  let numeratorBound :=
    2 * (numerator.radiusSq * denominatorCenterNorm +
      normSq numerator.center * denominator.radiusSq)
  let denominatorBound := apart.lowerSq * denominatorCenterNorm
  have denominatorCenterPositive : 0 < denominatorCenterNorm :=
    normSq_pos centerNonzero
  have denominatorBoundPositive : 0 < denominatorBound :=
    RFAP.ConstructiveFraction.mul_pos_direct apart.positive
      denominatorCenterPositive
  have numeratorDifference :
      x * denominator.center - numerator.center * y =
        (x - numerator.center) * denominator.center -
          numerator.center * (y - denominator.center) := by
    apply RFAP.ConstructiveGaussian.Gaussian.ext <;>
      simp only [sub_re, sub_im, mul_re, mul_im] <;> ring1
  have numeratorEstimate :
      normSq (x * denominator.center - numerator.center * y) ≤
        numeratorBound := by
    rw [numeratorDifference]
    calc
      normSq ((x - numerator.center) * denominator.center -
          numerator.center * (y - denominator.center)) ≤
          2 *
            (normSq ((x - numerator.center) * denominator.center) +
              normSq (numerator.center *
                (y - denominator.center))) := normSq_sub_le_two _ _
      _ = 2 *
          (normSq (x - numerator.center) * denominatorCenterNorm +
            normSq numerator.center *
              normSq (y - denominator.center)) := by
        rw [normSq_mul, normSq_mul]
      _ ≤ numeratorBound := by
        dsimp only [numeratorBound]
        apply RFAP.ConstructiveFraction.mul_le_mul_of_nonneg_left_direct
        · exact add_le_add
            (RFAP.ConstructiveFraction.mul_le_mul_of_nonneg_right_direct
              xInside (normSq_nonneg denominator.center))
            (RFAP.ConstructiveFraction.mul_le_mul_of_nonneg_left_direct
              yInside (normSq_nonneg numerator.center))
        · decide
  have denominatorEstimate : denominatorBound ≤
      normSq y * denominatorCenterNorm :=
    RFAP.ConstructiveFraction.mul_le_mul_of_nonneg_right_direct
      (apart.lower yInside) (normSq_nonneg denominator.center)
  have quotientIdentity :
      x / y - numerator.center / denominator.center =
        (x * denominator.center - numerator.center * y) /
          (y * denominator.center) := by
    exact gaussian_div_sub_div_direct x numerator.center y denominator.center
      yNonzero centerNonzero
  unfold Contains div
  dsimp only
  rw [quotientIdentity, normSq_div _ _
    (mul_ne_zero_direct yNonzero centerNonzero), normSq_mul]
  have exactDenominatorPositive :
      0 < normSq y * denominatorCenterNorm :=
    RFAP.ConstructiveFraction.mul_pos_direct (normSq_pos yNonzero)
      denominatorCenterPositive
  calc
    normSq (x * denominator.center - numerator.center * y) *
          (normSq y * denominatorCenterNorm)⁻¹ =
        normSq (x * denominator.center - numerator.center * y) /
          (normSq y * denominatorCenterNorm) := by
      rfl
    _ ≤ numeratorBound / (normSq y * denominatorCenterNorm) := by
      apply (RFAP.ConstructiveFraction.div_le_iff_pos
        exactDenominatorPositive).2
      calc
        normSq (x * denominator.center - numerator.center * y) ≤
            numeratorBound := numeratorEstimate
        _ = (numeratorBound / (normSq y * denominatorCenterNorm)) *
            (normSq y * denominatorCenterNorm) :=
          (RFAP.ConstructiveFraction.div_mul_cancel_of_ne numeratorBound
            (normSq y * denominatorCenterNorm)
            exactDenominatorPositive.ne').symm
    _ ≤ numeratorBound / denominatorBound :=
      RFAP.ConstructiveFraction.div_le_div_of_nonneg_left_direct
        (by
          exact RFAP.ConstructiveFraction.mul_nonneg_direct (by decide)
            (add_nonneg
              (RFAP.ConstructiveFraction.mul_nonneg_direct
                numerator.radiusSq_nonneg
                (normSq_nonneg denominator.center))
              (RFAP.ConstructiveFraction.mul_nonneg_direct
                (normSq_nonneg numerator.center)
                denominator.radiusSq_nonneg)))
        denominatorBoundPositive denominatorEstimate

end Ball

end CCL.ArithmeticEnclosures
