import mathlib.Tactic.QuotientFreeRing
import RFAP.Geometry.PathClearance
import RFAP.Polynomial.Bounds

/-!
# Quantitative clearance on constructive box boundaries

Path certificates on horizontal and vertical lines are converted to geometric
side certificates.  Four finite positive bounds combine by minimum into one
box-boundary certificate.
-/

namespace RFAP.BoxClearance

abbrev Coordinate := RFAP.ConstructiveFraction.Rational
abbrev Gaussian := RFAP.ConstructiveGaussian.Gaussian
abbrev GaussianPolynomial := RFAP.ConstructivePolynomial.GaussianPolynomial
abbrev Polynomial := RFAP.ComputablePolynomial.DensePolynomial Coordinate
abbrev Box := RFAP.Boxes.Box

open RFAP.ConstructiveGaussian.Gaussian
open RFAP.PathPolynomial
open RFAP.Winding
open RFAP.PathClearance

/-- Exact coordinate predicate for the boundary of a constructive box. -/
def OnBoxBoundary (box : Box) (z : Gaussian) : Prop :=
  box.Contains z ∧
    (z.re = box.xLower ∨ z.re = box.xUpper ∨
      z.im = box.yLower ∨ z.im = box.yUpper)

instance onBoxBoundaryDecidable (box : Box) (z : Gaussian) :
    Decidable (OnBoxBoundary box z) := by
  unfold OnBoxBoundary
  infer_instance

/-- A positive squared-norm lower bound on all four sides. -/
structure BoundaryClearance
    (p : GaussianPolynomial) (box : Box) where
  bound : Coordinate
  positive : 0 < bound
  lower : ∀ z : Gaussian, OnBoxBoundary box z →
    bound ≤ normSq (p.eval z)

namespace BoundaryClearance

/-- A clearance for the normalized finite coefficient list is also a
clearance for the original representation. -/
def ofNormalize
    {p : GaussianPolynomial} {box : Box}
    (clearance : BoundaryClearance p.normalize box) :
    BoundaryClearance p box where
  bound := clearance.bound
  positive := clearance.positive
  lower := by
    intro z boundary
    simpa only [RFAP.ComputablePolynomial.DensePolynomial.eval_normalize]
      using clearance.lower z boundary

/-- Quantitative boundary clearance is closed under polynomial
multiplication.  The displayed lower bound is the product of the two finite
lower bounds. -/
def mul
    {p q : GaussianPolynomial} {box : Box}
    (left : BoundaryClearance p box)
    (right : BoundaryClearance q box) : BoundaryClearance (p * q) box where
  bound := left.bound * right.bound
  positive := RFAP.ConstructiveFraction.mul_pos_direct
    left.positive right.positive
  lower := by
    intro z boundary
    rw [RFAP.ComputablePolynomial.DensePolynomial.eval_mul, normSq_mul]
    exact RFAP.ConstructiveFraction.mul_le_mul_direct
      (left.lower z boundary) (right.lower z boundary)
      right.positive.le
      (normSq_nonneg (p.eval z))

end BoundaryClearance

/-- A root inside a box with clear boundary is strictly inside every side. -/
theorem BoundaryClearance.root_strictContains
    {p : GaussianPolynomial} {box : Box}
    (clearance : BoundaryClearance p box) {z : Gaussian}
    (contains : box.Contains z) (root : p.eval z = 0) :
    box.StrictContains z := by
  have notBoundary : ¬OnBoxBoundary box z := by
    intro boundary
    have lower := clearance.lower z boundary
    rw [root, normSq_zero] at lower
    exact (not_lt_of_ge lower) clearance.positive
  refine ⟨lt_of_le_of_ne contains.1 ?_, lt_of_le_of_ne contains.2.1 ?_,
    lt_of_le_of_ne contains.2.2.1 ?_,
    lt_of_le_of_ne contains.2.2.2 ?_⟩
  · intro equal
    exact notBoundary ⟨contains, Or.inl equal.symm⟩
  · intro equal
    exact notBoundary ⟨contains, Or.inr (Or.inl equal)⟩
  · intro equal
    exact notBoundary
      ⟨contains, Or.inr (Or.inr (Or.inl equal.symm))⟩
  · intro equal
    exact notBoundary ⟨contains, Or.inr (Or.inr (Or.inr equal))⟩

/-- A displayed rational point whose actual residual is strictly below the
boundary clearance is strictly inside whenever it is weakly contained.  The
point need not be a polynomial root. -/
theorem BoundaryClearance.strictContains_of_residual_lt
    {p : GaussianPolynomial} {box : Box}
    (clearance : BoundaryClearance p box) {z : Gaussian}
    (contains : box.Contains z)
    (residualSmall : normSq (p.eval z) < clearance.bound) :
    box.StrictContains z := by
  have notBoundary : ¬OnBoxBoundary box z := by
    intro boundary
    have lower := clearance.lower z boundary
    exact (not_lt_of_ge lower) residualSmall
  refine ⟨lt_of_le_of_ne contains.1 ?_, lt_of_le_of_ne contains.2.1 ?_,
    lt_of_le_of_ne contains.2.2.1 ?_,
    lt_of_le_of_ne contains.2.2.2 ?_⟩
  · intro equal
    exact notBoundary ⟨contains, Or.inl equal.symm⟩
  · intro equal
    exact notBoundary ⟨contains, Or.inr (Or.inl equal)⟩
  · intro equal
    exact notBoundary
      ⟨contains, Or.inr (Or.inr (Or.inl equal.symm))⟩
  · intro equal
    exact notBoundary ⟨contains, Or.inr (Or.inr (Or.inr equal))⟩

namespace BoundaryClearance

/-- A positive rational strip width on which the polynomial Lipschitz budget
is at most one quarter of the boundary clearance. -/
def residualInteriorRadius
    {p : GaussianPolynomial} {box : Box}
    (clearance : BoundaryClearance p box) : Coordinate :=
  min 1
    (clearance.bound /
      (4 * RFAP.PolynomialBounds.denseLipschitzBound p box))

theorem residualInteriorRadius_pos
    {p : GaussianPolynomial} {box : Box}
    (clearance : BoundaryClearance p box) :
    0 < clearance.residualInteriorRadius := by
  exact lt_min (by decide)
    (RFAP.ConstructiveFraction.div_pos_direct clearance.positive
      (RFAP.ConstructiveFraction.mul_pos_direct (by decide)
        (RFAP.PolynomialBounds.denseLipschitzBound_pos p box)))

/-- The computed strip radius makes the full Lipschitz variation no larger
than one quarter of the boundary clearance. -/
theorem denseLipschitz_mul_residualInteriorRadius_sq_le
    {p : GaussianPolynomial} {box : Box}
    (clearance : BoundaryClearance p box) :
    RFAP.PolynomialBounds.denseLipschitzBound p box *
        clearance.residualInteriorRadius ^ 2 ≤
      clearance.bound / 4 := by
  let radius := clearance.residualInteriorRadius
  let lipschitz :=
    RFAP.PolynomialBounds.denseLipschitzBound p box
  have radiusPositive : 0 < radius := by
    simpa only [radius] using clearance.residualInteriorRadius_pos
  have radiusLeOne : radius ≤ 1 := min_le_left _ _
  have radiusLeRatio : radius ≤ clearance.bound / (4 * lipschitz) := by
    simpa only [radius, residualInteriorRadius, lipschitz] using
      (min_le_right 1
        (clearance.bound /
          (4 * RFAP.PolynomialBounds.denseLipschitzBound p box)))
  have radiusSqLeRadius : radius ^ 2 ≤ radius := by
    rw [pow_two]
    exact
      (RFAP.ConstructiveFraction.mul_le_mul_of_nonneg_right_direct
        radiusLeOne radiusPositive.le).trans_eq
          (RFAP.ConstructiveFraction.one_mul radius)
  have lipschitzPositive : 0 < lipschitz := by
    simpa only [lipschitz] using
      RFAP.PolynomialBounds.denseLipschitzBound_pos p box
  have fourPositive : (0 : Coordinate) < 4 := by decide
  have denominatorPositive : 0 < 4 * lipschitz :=
    RFAP.ConstructiveFraction.mul_pos_direct fourPositive lipschitzPositive
  have radiusScaled : radius * (4 * lipschitz) ≤ clearance.bound :=
    (RFAP.ConstructiveFraction.le_div_iff_pos denominatorPositive).1
      radiusLeRatio
  have lipschitzRadiusLeQuarter :
      lipschitz * radius ≤ clearance.bound / 4 := by
    apply (RFAP.ConstructiveFraction.le_div_iff_pos fourPositive).2
    calc
      lipschitz * radius * 4 = radius * (4 * lipschitz) := by ring1
      _ ≤ clearance.bound := radiusScaled
  exact (RFAP.ConstructiveFraction.mul_le_mul_of_nonneg_left_direct
    radiusSqLeRadius lipschitzPositive.le).trans lipschitzRadiusLeQuarter

private theorem quarter_add_quarter (target : Coordinate) :
    target / 4 + target / 4 = target / 2 := by
  apply RFAP.ConstructiveFraction.mul_right_cancel_of_ne
    (show (4 : Coordinate) ≠ 0 by decide)
  calc
    (target / 4 + target / 4) * 4 =
        (target / 4) * 4 + (target / 4) * 4 := by rw [add_mul]
    _ = target + target := by
      rw [show target / 4 * 4 = target from
        RFAP.ConstructiveFraction.div_mul_cancel_of_ne target 4 (by decide)]
    _ = target * 2 := by ring1
    _ = ((target / 2) * 2) * 2 := by
      rw [show target / 2 * 2 = target from
        RFAP.ConstructiveFraction.div_mul_cancel_of_ne target 2 (by decide)]
    _ = (target / 2) * (2 * 2) :=
      RFAP.ConstructiveFraction.mul_assoc (target / 2) 2 2
    _ = (target / 2) * 4 := by
      rw [show (2 : Coordinate) * 2 = 4 by decide]

private theorem two_mul_half (target : Coordinate) :
    2 * (target / 2) = target := by
  calc
    2 * (target / 2) = (target / 2) * 2 :=
      RFAP.ConstructiveFraction.mul_comm 2 (target / 2)
    _ = target :=
      RFAP.ConstructiveFraction.div_mul_cancel_of_ne target 2 (by decide)

/-- Two Gaussian terms respectively below and at one quarter of a positive
target have sum squared norm strictly below that target. -/
theorem normSq_add_lt_of_quarters
    {left right : Gaussian} {target : Coordinate}
    (leftSmall : normSq left < target / 4)
    (rightSmall : normSq right ≤ target / 4) :
    normSq (left + right) < target := by
  have valueUpper := normSq_add_le_two left right
  have sumStrict : normSq left + normSq right < target / 2 := by
    have first := RFAP.ConstructiveFraction.add_lt_add_right_direct leftSmall
      (normSq right)
    have second : target / 4 + normSq right ≤
        target / 4 + target / 4 := by
      calc
        target / 4 + normSq right = normSq right + target / 4 :=
          RFAP.ConstructiveFraction.add_comm _ _
        _ ≤ target / 4 + target / 4 :=
          RFAP.ConstructiveFraction.add_le_add_right_direct rightSmall
            (target / 4)
    exact (first.trans_le second).trans_eq (quarter_add_quarter target)
  have twiceStrict : 2 * (normSq left + normSq right) < target := by
    have scaled := RFAP.ConstructiveFraction.mul_lt_mul_of_pos_left_direct
      (show (0 : Coordinate) < 2 by decide) sumStrict
    calc
      2 * (normSq left + normSq right) < 2 * (target / 2) := scaled
      _ = target := two_mul_half target
  exact valueUpper.trans_lt twiceStrict

/-- A point with residual below one quarter of the boundary clearance cannot
be within the computed squared distance of any displayed boundary point. -/
theorem residualInteriorRadius_sq_lt_normSq_sub
    {p : GaussianPolynomial} {box : Box}
    (clearance : BoundaryClearance p box) {z w : Gaussian}
    (contains : box.Contains z) (boundary : OnBoxBoundary box w)
    (residualSmall : normSq (p.eval z) < clearance.bound / 4) :
    clearance.residualInteriorRadius ^ 2 < normSq (w - z) := by
  let radius := clearance.residualInteriorRadius
  match RFAP.ConstructiveFraction.rationalDecLT
      (radius ^ 2) (normSq (w - z)) with
  | isTrue far => exact far
  | isFalse far =>
    have distanceLe : normSq (w - z) ≤ radius ^ 2 := le_of_not_gt far
    have variation :=
      RFAP.PolynomialBounds.normSq_eval_sub_eval_le_denseLipschitzBound
        p boundary.1 contains
    have variationQuarter : normSq (p.eval w - p.eval z) ≤
        clearance.bound / 4 := by
      calc
        normSq (p.eval w - p.eval z) ≤
            RFAP.PolynomialBounds.denseLipschitzBound p box *
              normSq (w - z) := variation
        _ ≤ RFAP.PolynomialBounds.denseLipschitzBound p box *
            radius ^ 2 :=
          RFAP.ConstructiveFraction.mul_le_mul_of_nonneg_left_direct distanceLe
            (RFAP.PolynomialBounds.denseLipschitzBound_pos p box).le
        _ ≤ clearance.bound / 4 := by
          simpa only [radius] using
            clearance.denseLipschitz_mul_residualInteriorRadius_sq_le
    have boundaryStrict : normSq (p.eval w) < clearance.bound := by
      have sumStrict := normSq_add_lt_of_quarters residualSmall variationQuarter
      have valueIdentity : p.eval w = p.eval z + (p.eval w - p.eval z) := by
        apply RFAP.ConstructiveGaussian.Gaussian.ext <;>
          simp only [add_re, add_im, sub_re, sub_im] <;> ring1
      rw [valueIdentity]
      exact sumStrict
    exact ((not_lt_of_ge (clearance.lower w boundary)) boundaryStrict).elim

/-- The same residual test yields one uniform strict margin from all four
sides of the rational box. -/
theorem residualInteriorMargins
    {p : GaussianPolynomial} {box : Box}
    (clearance : BoundaryClearance p box) {z : Gaussian}
    (contains : box.Contains z)
    (residualSmall : normSq (p.eval z) < clearance.bound / 4) :
    let radius := clearance.residualInteriorRadius
    box.xLower + radius < z.re ∧
      z.re + radius < box.xUpper ∧
      box.yLower + radius < z.im ∧
      z.im + radius < box.yUpper := by
  let radius := clearance.residualInteriorRadius
  have radiusPositive : 0 < radius := by
    simpa only [radius] using clearance.residualInteriorRadius_pos
  have far {w : Gaussian} (boundary : OnBoxBoundary box w) :
      radius ^ 2 < normSq (w - z) := by
    simpa only [radius] using
      clearance.residualInteriorRadius_sq_lt_normSq_sub contains boundary
        residualSmall
  have left : box.xLower + radius < z.re := by
    match RFAP.ConstructiveFraction.rationalDecLT
        (box.xLower + radius) z.re with
    | isTrue strict => exact strict
    | isFalse strict =>
      have gapLe : z.re - box.xLower ≤ radius := by
        apply RFAP.ConstructiveFraction.le_of_add_le_add_right_direct
          (c := box.xLower)
        calc
          (z.re - box.xLower) + box.xLower = z.re := by ring1
          _ ≤ box.xLower + radius := le_of_not_gt strict
          _ = radius + box.xLower := by ring1
      have gapNonnegative : 0 ≤ z.re - box.xLower := sub_nonneg.mpr contains.1
      let w : Gaussian := ⟨box.xLower, z.im⟩
      have boundary : OnBoxBoundary box w :=
        ⟨⟨le_rfl, box.x_valid, contains.2.2.1, contains.2.2.2⟩,
          Or.inl rfl⟩
      have distanceLe : normSq (w - z) ≤ radius ^ 2 := by
        have squareLe := RFAP.ConstructiveFraction.pow_le_pow_direct
          gapNonnegative gapLe 2
        calc
          normSq (w - z) = (z.re - box.xLower) ^ 2 := by
            dsimp only [w, normSq, sub_re, sub_im]
            ring1
          _ ≤ radius ^ 2 := squareLe
      exact ((not_lt_of_ge distanceLe) (far boundary)).elim
  have right : z.re + radius < box.xUpper := by
    match RFAP.ConstructiveFraction.rationalDecLT
        (z.re + radius) box.xUpper with
    | isTrue strict => exact strict
    | isFalse strict =>
      have gapLe : box.xUpper - z.re ≤ radius := by
        apply RFAP.ConstructiveFraction.le_of_add_le_add_right_direct
          (c := z.re)
        calc
          (box.xUpper - z.re) + z.re = box.xUpper := by ring1
          _ ≤ z.re + radius := le_of_not_gt strict
          _ = radius + z.re := by ring1
      have gapNonnegative : 0 ≤ box.xUpper - z.re :=
        sub_nonneg.mpr contains.2.1
      let w : Gaussian := ⟨box.xUpper, z.im⟩
      have boundary : OnBoxBoundary box w :=
        ⟨⟨box.x_valid, le_rfl, contains.2.2.1, contains.2.2.2⟩,
          Or.inr (Or.inl rfl)⟩
      have distanceLe : normSq (w - z) ≤ radius ^ 2 := by
        have squareLe := RFAP.ConstructiveFraction.pow_le_pow_direct
          gapNonnegative gapLe 2
        calc
          normSq (w - z) = (box.xUpper - z.re) ^ 2 := by
            dsimp only [w, normSq, sub_re, sub_im]
            ring1
          _ ≤ radius ^ 2 := squareLe
      exact ((not_lt_of_ge distanceLe) (far boundary)).elim
  have bottom : box.yLower + radius < z.im := by
    match RFAP.ConstructiveFraction.rationalDecLT
        (box.yLower + radius) z.im with
    | isTrue strict => exact strict
    | isFalse strict =>
      have gapLe : z.im - box.yLower ≤ radius := by
        apply RFAP.ConstructiveFraction.le_of_add_le_add_right_direct
          (c := box.yLower)
        calc
          (z.im - box.yLower) + box.yLower = z.im := by ring1
          _ ≤ box.yLower + radius := le_of_not_gt strict
          _ = radius + box.yLower := by ring1
      have gapNonnegative : 0 ≤ z.im - box.yLower :=
        sub_nonneg.mpr contains.2.2.1
      let w : Gaussian := ⟨z.re, box.yLower⟩
      have boundary : OnBoxBoundary box w :=
        ⟨⟨contains.1, contains.2.1, le_rfl, box.y_valid⟩,
          Or.inr (Or.inr (Or.inl rfl))⟩
      have distanceLe : normSq (w - z) ≤ radius ^ 2 := by
        have squareLe := RFAP.ConstructiveFraction.pow_le_pow_direct
          gapNonnegative gapLe 2
        calc
          normSq (w - z) = (z.im - box.yLower) ^ 2 := by
            dsimp only [w, normSq, sub_re, sub_im]
            ring1
          _ ≤ radius ^ 2 := squareLe
      exact ((not_lt_of_ge distanceLe) (far boundary)).elim
  have top : z.im + radius < box.yUpper := by
    match RFAP.ConstructiveFraction.rationalDecLT
        (z.im + radius) box.yUpper with
    | isTrue strict => exact strict
    | isFalse strict =>
      have gapLe : box.yUpper - z.im ≤ radius := by
        apply RFAP.ConstructiveFraction.le_of_add_le_add_right_direct
          (c := z.im)
        calc
          (box.yUpper - z.im) + z.im = box.yUpper := by ring1
          _ ≤ z.im + radius := le_of_not_gt strict
          _ = radius + z.im := by ring1
      have gapNonnegative : 0 ≤ box.yUpper - z.im :=
        sub_nonneg.mpr contains.2.2.2
      let w : Gaussian := ⟨z.re, box.yUpper⟩
      have boundary : OnBoxBoundary box w :=
        ⟨⟨contains.1, contains.2.1, box.y_valid, le_rfl⟩,
          Or.inr (Or.inr (Or.inr rfl))⟩
      have distanceLe : normSq (w - z) ≤ radius ^ 2 := by
        have squareLe := RFAP.ConstructiveFraction.pow_le_pow_direct
          gapNonnegative gapLe 2
        calc
          normSq (w - z) = (box.yUpper - z.im) ^ 2 := by
            dsimp only [w, normSq, sub_re, sub_im]
            ring1
          _ ≤ radius ^ 2 := squareLe
      exact ((not_lt_of_ge distanceLe) (far boundary)).elim
  exact ⟨left, right, bottom, top⟩

end BoundaryClearance

structure VerticalLineClearance
    (p : GaussianPolynomial) (ambient : Box) (x : Coordinate) where
  bound : Coordinate
  positive : 0 < bound
  lower : ∀ y : Coordinate,
    ambient.yLower ≤ y → y ≤ ambient.yUpper →
    bound ≤ normSq (p.eval (point x y))

structure HorizontalLineClearance
    (p : GaussianPolynomial) (ambient : Box) (y : Coordinate) where
  bound : Coordinate
  positive : 0 < bound
  lower : ∀ x : Coordinate,
    ambient.xLower ≤ x → x ≤ ambient.xUpper →
    bound ≤ normSq (p.eval (point x y))

namespace VerticalLineClearance

/-- Vertical-line clearance is closed under polynomial multiplication. -/
def mul
    {p q : GaussianPolynomial} {ambient : Box} {x : Coordinate}
    (left : VerticalLineClearance p ambient x)
    (right : VerticalLineClearance q ambient x) :
    VerticalLineClearance (p * q) ambient x where
  bound := left.bound * right.bound
  positive := RFAP.ConstructiveFraction.mul_pos_direct
    left.positive right.positive
  lower := by
    intro y lower upper
    rw [RFAP.ComputablePolynomial.DensePolynomial.eval_mul, normSq_mul]
    exact RFAP.ConstructiveFraction.mul_le_mul_direct
      (left.lower y lower upper) (right.lower y lower upper)
      right.positive.le (normSq_nonneg _)

end VerticalLineClearance

namespace HorizontalLineClearance

/-- Horizontal-line clearance is closed under polynomial multiplication. -/
def mul
    {p q : GaussianPolynomial} {ambient : Box} {y : Coordinate}
    (left : HorizontalLineClearance p ambient y)
    (right : HorizontalLineClearance q ambient y) :
    HorizontalLineClearance (p * q) ambient y where
  bound := left.bound * right.bound
  positive := RFAP.ConstructiveFraction.mul_pos_direct
    left.positive right.positive
  lower := by
    intro x lower upper
    rw [RFAP.ComputablePolynomial.DensePolynomial.eval_mul, normSq_mul]
    exact RFAP.ConstructiveFraction.mul_le_mul_direct
      (left.lower x lower upper) (right.lower x lower upper)
      right.positive.le (normSq_nonneg _)

end HorizontalLineClearance

/-- Convert geometric vertical-line clearance back to the exact affine path
certificate used by the finite Cauchy construction. -/
def VerticalLineClearance.toPathCertificate
    {p : GaussianPolynomial} {ambient : Box} {x : Coordinate}
    (clearance : VerticalLineClearance p ambient x) :
    Certificate
      (pathReal p (verticalBase x) verticalDirection)
      (pathImag p (verticalBase x) verticalDirection)
      ⟨ambient.yLower, ambient.yUpper, ambient.y_valid⟩ where
  bound := clearance.bound
  positive := clearance.positive
  lower := by
    intro y inside
    have bound := clearance.lower y inside.1 inside.2
    simpa only [normSq, eval_pathReal, eval_pathImag, line_vertical]
      using bound

@[simp] theorem VerticalLineClearance.toPathCertificate_bound
    {p : GaussianPolynomial} {ambient : Box} {x : Coordinate}
    (clearance : VerticalLineClearance p ambient x) :
    clearance.toPathCertificate.bound = clearance.bound := rfl

/-- Convert geometric horizontal-line clearance back to the exact affine
path certificate used by the finite Cauchy construction. -/
def HorizontalLineClearance.toPathCertificate
    {p : GaussianPolynomial} {ambient : Box} {y : Coordinate}
    (clearance : HorizontalLineClearance p ambient y) :
    Certificate
      (pathReal p (horizontalBase y) horizontalDirection)
      (pathImag p (horizontalBase y) horizontalDirection)
      ⟨ambient.xLower, ambient.xUpper, ambient.x_valid⟩ where
  bound := clearance.bound
  positive := clearance.positive
  lower := by
    intro x inside
    have bound := clearance.lower x inside.1 inside.2
    simpa only [normSq, eval_pathReal, eval_pathImag, line_horizontal]
      using bound

@[simp] theorem HorizontalLineClearance.toPathCertificate_bound
    {p : GaussianPolynomial} {ambient : Box} {y : Coordinate}
    (clearance : HorizontalLineClearance p ambient y) :
    clearance.toPathCertificate.bound = clearance.bound := rfl

/-- Boundary clearance makes every displayed boundary evaluation nonzero. -/
theorem BoundaryClearance.eval_ne_zero
    {p : GaussianPolynomial} {box : Box}
    (clearance : BoundaryClearance p box) {z : Gaussian}
    (boundary : OnBoxBoundary box z) : p.eval z ≠ 0 := by
  intro zero
  have lower := clearance.lower z boundary
  rw [zero, normSq_zero] at lower
  exact (not_lt_of_ge lower) clearance.positive

def VerticalLineClearance.restrict
    {p : GaussianPolynomial} {ambient small : Box} {x : Coordinate}
    (clearance : VerticalLineClearance p ambient x)
    (refines : small.Refines ambient) : VerticalLineClearance p small x where
  bound := clearance.bound
  positive := clearance.positive
  lower := fun y lower upper => clearance.lower y
    (refines.2.2.1.trans lower) (upper.trans refines.2.2.2)

@[simp] theorem VerticalLineClearance.restrict_bound
    {p : GaussianPolynomial} {ambient small : Box} {x : Coordinate}
    (clearance : VerticalLineClearance p ambient x)
    (refines : small.Refines ambient) :
    (clearance.restrict refines).bound = clearance.bound := rfl

def HorizontalLineClearance.restrict
    {p : GaussianPolynomial} {ambient small : Box} {y : Coordinate}
    (clearance : HorizontalLineClearance p ambient y)
    (refines : small.Refines ambient) : HorizontalLineClearance p small y where
  bound := clearance.bound
  positive := clearance.positive
  lower := fun x lower upper => clearance.lower x
    (refines.1.trans lower) (upper.trans refines.2.1)

@[simp] theorem HorizontalLineClearance.restrict_bound
    {p : GaussianPolynomial} {ambient small : Box} {y : Coordinate}
    (clearance : HorizontalLineClearance p ambient y)
    (refines : small.Refines ambient) :
    (clearance.restrict refines).bound = clearance.bound := rfl

def verticalInterval (ambient : Box) : Interval where
  lower := ambient.yLower
  upper := ambient.yUpper
  valid := ambient.y_valid

def horizontalInterval (ambient : Box) : Interval where
  lower := ambient.xLower
  upper := ambient.xUpper
  valid := ambient.x_valid

/-- Convert a finite coordinate-path certificate for `x + it` into geometric
vertical-line clearance. -/
def verticalOfPathCertificate
    (p : GaussianPolynomial) (ambient : Box) (x : Coordinate)
    (certificate : Certificate
      (pathReal p (verticalBase x) verticalDirection)
      (pathImag p (verticalBase x) verticalDirection)
      (verticalInterval ambient)) : VerticalLineClearance p ambient x where
  bound := certificate.bound
  positive := certificate.positive
  lower := by
    intro y lower upper
    have bound := certificate.lower y ⟨lower, upper⟩
    simpa only [normSq, eval_pathReal, eval_pathImag, line_vertical]
      using bound

@[simp] theorem verticalOfPathCertificate_bound
    (p : GaussianPolynomial) (ambient : Box) (x : Coordinate)
    (certificate : Certificate
      (pathReal p (verticalBase x) verticalDirection)
      (pathImag p (verticalBase x) verticalDirection)
      (verticalInterval ambient)) :
    (verticalOfPathCertificate p ambient x certificate).bound =
      certificate.bound := rfl

/-- Convert a finite coordinate-path certificate for `t + iy` into geometric
horizontal-line clearance. -/
def horizontalOfPathCertificate
    (p : GaussianPolynomial) (ambient : Box) (y : Coordinate)
    (certificate : Certificate
      (pathReal p (horizontalBase y) horizontalDirection)
      (pathImag p (horizontalBase y) horizontalDirection)
      (horizontalInterval ambient)) : HorizontalLineClearance p ambient y where
  bound := certificate.bound
  positive := certificate.positive
  lower := by
    intro x lower upper
    have bound := certificate.lower x ⟨lower, upper⟩
    simpa only [normSq, eval_pathReal, eval_pathImag, line_horizontal]
      using bound

@[simp] theorem horizontalOfPathCertificate_bound
    (p : GaussianPolynomial) (ambient : Box) (y : Coordinate)
    (certificate : Certificate
      (pathReal p (horizontalBase y) horizontalDirection)
      (pathImag p (horizontalBase y) horizontalDirection)
      (horizontalInterval ambient)) :
    (horizontalOfPathCertificate p ambient y certificate).bound =
      certificate.bound := rfl

/-- A displayed finite Bézout certificate produces vertical-line clearance. -/
def verticalOfCoprime
    (p : GaussianPolynomial) (ambient : Box) (x : Coordinate)
    (coprime : CoprimeCertificate
      (pathReal p (verticalBase x) verticalDirection)
      (pathImag p (verticalBase x) verticalDirection)) :
    VerticalLineClearance p ambient x :=
  verticalOfPathCertificate p ambient x
    (certificateOfCoprime coprime (verticalInterval ambient))

/-- A displayed finite Bézout certificate produces horizontal-line clearance. -/
def horizontalOfCoprime
    (p : GaussianPolynomial) (ambient : Box) (y : Coordinate)
    (coprime : CoprimeCertificate
      (pathReal p (horizontalBase y) horizontalDirection)
      (pathImag p (horizontalBase y) horizontalDirection)) :
    HorizontalLineClearance p ambient y :=
  horizontalOfPathCertificate p ambient y
    (certificateOfCoprime coprime (horizontalInterval ambient))

def leftOfBoundary
    {p : GaussianPolynomial} {box : Box}
    (clearance : BoundaryClearance p box) :
    VerticalLineClearance p box box.xLower where
  bound := clearance.bound
  positive := clearance.positive
  lower := by
    intro y lower upper
    apply clearance.lower
    exact ⟨⟨le_rfl, box.x_valid, lower, upper⟩, Or.inl rfl⟩

def rightOfBoundary
    {p : GaussianPolynomial} {box : Box}
    (clearance : BoundaryClearance p box) :
    VerticalLineClearance p box box.xUpper where
  bound := clearance.bound
  positive := clearance.positive
  lower := by
    intro y lower upper
    apply clearance.lower
    exact ⟨⟨box.x_valid, le_rfl, lower, upper⟩,
      Or.inr (Or.inl rfl)⟩

def bottomOfBoundary
    {p : GaussianPolynomial} {box : Box}
    (clearance : BoundaryClearance p box) :
    HorizontalLineClearance p box box.yLower where
  bound := clearance.bound
  positive := clearance.positive
  lower := by
    intro x lower upper
    apply clearance.lower
    exact ⟨⟨lower, upper, le_rfl, box.y_valid⟩,
      Or.inr (Or.inr (Or.inl rfl))⟩

def topOfBoundary
    {p : GaussianPolynomial} {box : Box}
    (clearance : BoundaryClearance p box) :
    HorizontalLineClearance p box box.yUpper where
  bound := clearance.bound
  positive := clearance.positive
  lower := by
    intro x lower upper
    apply clearance.lower
    exact ⟨⟨lower, upper, box.y_valid, le_rfl⟩,
      Or.inr (Or.inr (Or.inr rfl))⟩

/-- Four side certificates combine by a finite minimum. -/
def boundaryOfLines
    {p : GaussianPolynomial} {box : Box}
    (left : VerticalLineClearance p box box.xLower)
    (right : VerticalLineClearance p box box.xUpper)
    (bottom : HorizontalLineClearance p box box.yLower)
    (top : HorizontalLineClearance p box box.yUpper) :
    BoundaryClearance p box := by
  let bound := min left.bound (min right.bound (min bottom.bound top.bound))
  exact
    { bound := bound
      positive := lt_min left.positive
        (lt_min right.positive (lt_min bottom.positive top.positive))
      lower := by
        intro z boundary
        rcases boundary.1 with ⟨xLower, xUpper, yLower, yUpper⟩
        rcases boundary.2 with onLeft | onRight | onBottom | onTop
        · calc
            bound ≤ left.bound := min_le_left _ _
            _ ≤ normSq (p.eval z) := by
              have lower := left.lower z.im yLower yUpper
              have pointEq : point box.xLower z.im = z := by
                apply RFAP.ConstructiveGaussian.Gaussian.ext
                · exact onLeft.symm
                · rfl
              simpa only [pointEq] using lower

        · calc
            bound ≤ right.bound :=
              (min_le_right _ _).trans (min_le_left _ _)
            _ ≤ normSq (p.eval z) := by
              have lower := right.lower z.im yLower yUpper
              have pointEq : point box.xUpper z.im = z := by
                apply RFAP.ConstructiveGaussian.Gaussian.ext
                · exact onRight.symm
                · rfl
              simpa only [pointEq] using lower
        · calc
            bound ≤ bottom.bound :=
              (min_le_right _ _).trans
                ((min_le_right _ _).trans (min_le_left _ _))
            _ ≤ normSq (p.eval z) := by
              have lower := bottom.lower z.re xLower xUpper
              have pointEq : point z.re box.yLower = z := by
                apply RFAP.ConstructiveGaussian.Gaussian.ext
                · rfl
                · exact onBottom.symm
              simpa only [pointEq] using lower
        · calc
            bound ≤ top.bound :=
              (min_le_right _ _).trans
                ((min_le_right _ _).trans (min_le_right _ _))
            _ ≤ normSq (p.eval z) := by
              have lower := top.lower z.re xLower xUpper
              have pointEq : point z.re box.yUpper = z := by
                apply RFAP.ConstructiveGaussian.Gaussian.ext
                · rfl
                · exact onTop.symm
              simpa only [pointEq] using lower }

@[simp] theorem boundaryOfLines_bound
    {p : GaussianPolynomial} {box : Box}
    (left : VerticalLineClearance p box box.xLower)
    (right : VerticalLineClearance p box box.xUpper)
    (bottom : HorizontalLineClearance p box box.yLower)
    (top : HorizontalLineClearance p box box.yUpper) :
    (boundaryOfLines left right bottom top).bound =
      min left.bound (min right.bound (min bottom.bound top.bound)) := rfl

theorem boundaryOfLines_bound_le_left
    {p : GaussianPolynomial} {box : Box}
    (left : VerticalLineClearance p box box.xLower)
    (right : VerticalLineClearance p box box.xUpper)
    (bottom : HorizontalLineClearance p box box.yLower)
    (top : HorizontalLineClearance p box box.yUpper) :
    (boundaryOfLines left right bottom top).bound <= left.bound := by
  unfold boundaryOfLines
  exact min_le_left _ _

theorem boundaryOfLines_bound_le_right
    {p : GaussianPolynomial} {box : Box}
    (left : VerticalLineClearance p box box.xLower)
    (right : VerticalLineClearance p box box.xUpper)
    (bottom : HorizontalLineClearance p box box.yLower)
    (top : HorizontalLineClearance p box box.yUpper) :
    (boundaryOfLines left right bottom top).bound <= right.bound := by
  unfold boundaryOfLines
  exact (min_le_right _ _).trans (min_le_left _ _)

theorem boundaryOfLines_bound_le_bottom
    {p : GaussianPolynomial} {box : Box}
    (left : VerticalLineClearance p box box.xLower)
    (right : VerticalLineClearance p box box.xUpper)
    (bottom : HorizontalLineClearance p box box.yLower)
    (top : HorizontalLineClearance p box box.yUpper) :
    (boundaryOfLines left right bottom top).bound <= bottom.bound := by
  unfold boundaryOfLines
  exact (min_le_right _ _).trans
    ((min_le_right _ _).trans (min_le_left _ _))

theorem boundaryOfLines_bound_le_top
    {p : GaussianPolynomial} {box : Box}
    (left : VerticalLineClearance p box box.xLower)
    (right : VerticalLineClearance p box box.xUpper)
    (bottom : HorizontalLineClearance p box box.yLower)
    (top : HorizontalLineClearance p box box.yUpper) :
    (boundaryOfLines left right bottom top).bound <= top.bound := by
  unfold boundaryOfLines
  exact (min_le_right _ _).trans
    ((min_le_right _ _).trans (min_le_right _ _))

end RFAP.BoxClearance
