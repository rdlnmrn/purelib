module
public import Purelib.Polynomial.Dense.Gaussian.Bounds.Box
import Purelib.Data.Rat.Fraction
import Purelib.Data.Gaussian.Basic
import Purelib.Data.Gaussian.Norm.Basic
import Purelib.Data.Gaussian.Norm.Bounds
import Purelib.Data.Rat.Fraction.Decide
import Purelib.Data.Rat.Fraction.Field
import Purelib.Data.Rat.Fraction.Order.Arithmetic
import Purelib.Data.Rat.Fraction.Order.Field
import Purelib.Geometry.Rational.Box.Basic
import Purelib.Geometry.Rational.Box.Boundary
public import Purelib.Polynomial.Clearance.Box.Boundary.Basic
import Purelib.Polynomial.Dense.Gaussian.Basic
import Mathlib.Algebra.Ring.Defs
import Purelib.Data.Gaussian.Field
import Purelib.Data.Rat.Fraction.Arithmetic
import Purelib.Data.Rat.Fraction.Order.Basic
import Purelib.Polynomial.Dense.Evaluation
import Purelib.Tactic.Ring
import Purelib.Algebra.Group.Negation

/-!
# Residual clearance inside rational boxes

Boundary clearance and a finite polynomial Lipschitz coefficient determine
a positive interior strip and retain strict margins for displayed rational points.
-/

open Purelib.Algebra.Group in
attribute [local instance high] Negation.subNegZeroMonoid

namespace Purelib.Polynomial.Clearance.Box.Boundary.Basic.BoundaryClearance

open Purelib.Data
open Purelib.Data.Rat
open Purelib.Data.Rat.Fraction
open Purelib.Geometry.Rational
open Purelib.Polynomial

/-- A root inside a box with clear boundary is strictly inside every side.

Weak containment and vanishing polynomial evaluation exclude every boundary
side because the supplied clearance bound is strictly positive. -/
public theorem root_strictContains
    {p : Dense.Gaussian.Basic.CanonicalCoefficients.CoefficientPolynomial} {box : Box}
    (clearance : Clearance.Box.Boundary.Basic.BoundaryClearance p box) {z : Gaussian.Basic.Canonical}
    (contains : box.Contains z) (root : p.eval z = 0) :
    box.StrictContains z := by
  have notBoundary : ¬Box.Boundary.OnBoxBoundary box z := by
    intro boundary
    have lower := clearance.lower z boundary
    rw [root, Gaussian.Basic.Canonical.normSq_zero] at lower
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
point need not be a polynomial root.

Weak containment places the displayed point inside the closed box. Its
residual is below the retained boundary lower bound, excluding equality on any side. -/
public theorem strictContains_of_residual_lt
    {p : Dense.Gaussian.Basic.CanonicalCoefficients.CoefficientPolynomial} {box : Box}
    (clearance : Clearance.Box.Boundary.Basic.BoundaryClearance p box) {z : Gaussian.Basic.Canonical}
    (contains : box.Contains z)
    (residualSmall : Data.Gaussian.Norm.Basic.normSq (p.eval z) < clearance.bound) :
    box.StrictContains z := by
  have notBoundary : ¬Box.Boundary.OnBoxBoundary box z := by
    intro boundary
    have lower := clearance.lower z boundary
    rw [Gaussian.Norm.Basic.normSq_eq_canonical] at residualSmall
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

/-- A positive rational strip width on which the polynomial Lipschitz budget
is at most one quarter of the boundary clearance.

The minimum caps the strip width at one and at boundary clearance divided
by four times the positive box Lipschitz coefficient. -/
@[expose] public def residualInteriorRadius
    {p : Dense.Gaussian.Basic.CanonicalCoefficients.CoefficientPolynomial} {box : Box}
    (clearance : Clearance.Box.Boundary.Basic.BoundaryClearance p box) : Fraction.Rational :=
  min 1
    (clearance.bound /
      (4 * Dense.Gaussian.Bounds.Box.denseLipschitzBound p box))

/-- The strip radius computed from positive boundary clearance and the box Lipschitz bound is positive.

Both the initial cap one and the clearance-to-Lipschitz ratio are positive.
The retained rational minimum therefore selects a strictly positive width. -/
public theorem residualInteriorRadius_pos
    {p : Dense.Gaussian.Basic.CanonicalCoefficients.CoefficientPolynomial} {box : Box}
    (clearance : Clearance.Box.Boundary.Basic.BoundaryClearance p box) :
    0 < clearance.residualInteriorRadius := by
  exact Order.Basic.lt_min (by decide)
    (Order.Field.div_pos_direct clearance.positive
      (Order.Arithmetic.mul_pos_direct (by decide)
        (Dense.Gaussian.Bounds.Box.denseLipschitzBound_pos p box)))

/-- The computed strip radius makes the full Lipschitz variation no larger
than one quarter of the boundary clearance.

The strip width is at most one and at most the clearance-to-Lipschitz ratio.
These two bounds control its squared Lipschitz variation by the clearance quarter. -/
public theorem denseLipschitz_mul_residualInteriorRadius_sq_le
    {p : Dense.Gaussian.Basic.CanonicalCoefficients.CoefficientPolynomial} {box : Box}
    (clearance : Clearance.Box.Boundary.Basic.BoundaryClearance p box) :
    Dense.Gaussian.Bounds.Box.denseLipschitzBound p box *
        clearance.residualInteriorRadius ^ 2 ≤
      clearance.bound / 4 := by
  let radius := clearance.residualInteriorRadius
  let lipschitz :=
    Dense.Gaussian.Bounds.Box.denseLipschitzBound p box
  have radiusPositive : 0 < radius := by
    simpa only [radius] using clearance.residualInteriorRadius_pos
  have radiusLeOne : radius ≤ 1 := Order.Basic.min_le_left _ _
  have radiusLeRatio : radius ≤ clearance.bound / (4 * lipschitz) := by
    simpa only [radius, residualInteriorRadius, lipschitz] using
      (Order.Basic.min_le_right 1
        (clearance.bound /
          (4 * Dense.Gaussian.Bounds.Box.denseLipschitzBound p box)))
  have radiusSqLeRadius : radius ^ 2 ≤ radius := by
    rw [pow_two]
    exact
      (Order.Arithmetic.mul_le_mul_of_nonneg_right_direct
        radiusLeOne radiusPositive.le).trans_eq
          (Fraction.Field.one_mul radius)
  have lipschitzPositive : 0 < lipschitz := by
    simpa only [lipschitz] using
      Dense.Gaussian.Bounds.Box.denseLipschitzBound_pos p box
  have fourPositive : (0 : Fraction.Rational) < 4 := by decide
  have denominatorPositive : 0 < 4 * lipschitz :=
    Order.Arithmetic.mul_pos_direct fourPositive lipschitzPositive
  have radiusScaled : radius * (4 * lipschitz) ≤ clearance.bound :=
    (Order.Field.le_div_iff_pos denominatorPositive).1
      radiusLeRatio
  have lipschitzRadiusLeQuarter :
      lipschitz * radius ≤ clearance.bound / 4 := by
    apply (Order.Field.le_div_iff_pos fourPositive).2
    calc
      lipschitz * radius * 4 = radius * (4 * lipschitz) := by ring1
      _ ≤ clearance.bound := radiusScaled
  exact (Order.Arithmetic.mul_le_mul_of_nonneg_left_direct
    radiusSqLeRadius lipschitzPositive.le).trans lipschitzRadiusLeQuarter

/-- A point with residual below one quarter of the boundary clearance cannot
be within the computed squared distance of any displayed boundary point.

The displayed point is contained in the box and has residual below the
clearance quarter. A closer boundary point would contradict its retained clearance. -/
public theorem residualInteriorRadius_sq_lt_normSq_sub
    {p : Dense.Gaussian.Basic.CanonicalCoefficients.CoefficientPolynomial} {box : Box}
    (clearance : Clearance.Box.Boundary.Basic.BoundaryClearance p box) {z w : Gaussian.Basic.Canonical}
    (contains : box.Contains z) (boundary : Box.Boundary.OnBoxBoundary box w)
    (residualSmall : Data.Gaussian.Norm.Basic.normSq (p.eval z) < clearance.bound / 4) :
    clearance.residualInteriorRadius ^ 2 < Data.Gaussian.Norm.Basic.normSq (w - z) := by
  let radius := clearance.residualInteriorRadius
  match Fraction.Decide.rationalDecLT
      (radius ^ 2) (Data.Gaussian.Norm.Basic.normSq (w - z)) with
  | isTrue far => exact far
  | isFalse far =>
    have distanceLe : Data.Gaussian.Norm.Basic.normSq (w - z) ≤ radius ^ 2 := le_of_not_gt far
    have variation :=
      Dense.Gaussian.Bounds.Box.normSq_eval_sub_eval_le_denseLipschitzBound
        p boundary.1 contains
    have variationQuarter : Data.Gaussian.Norm.Basic.normSq (p.eval w - p.eval z) ≤
        clearance.bound / 4 := by
      calc
        Data.Gaussian.Norm.Basic.normSq (p.eval w - p.eval z) ≤
            Dense.Gaussian.Bounds.Box.denseLipschitzBound p box *
              Data.Gaussian.Norm.Basic.normSq (w - z) := variation
        _ ≤ Dense.Gaussian.Bounds.Box.denseLipschitzBound p box *
            radius ^ 2 :=
          Order.Arithmetic.mul_le_mul_of_nonneg_left_direct distanceLe
            (Dense.Gaussian.Bounds.Box.denseLipschitzBound_pos p box).le
        _ ≤ clearance.bound / 4 := by
          simpa only [radius] using
            clearance.denseLipschitz_mul_residualInteriorRadius_sq_le
    have boundaryStrict : Data.Gaussian.Norm.Basic.normSq (p.eval w) < clearance.bound := by
      have sumStrict := normSq_add_lt_of_quarters residualSmall variationQuarter
      have valueIdentity : p.eval w = p.eval z + (p.eval w - p.eval z) := by
        apply Gaussian.Basic.ext <;>
          simp only [Gaussian.Basic.add_re, Gaussian.Basic.add_im, Gaussian.Basic.sub_re, Gaussian.Basic.sub_im] <;>
            ring1
      rw [valueIdentity]
      exact sumStrict
    rw [Gaussian.Norm.Basic.normSq_eq_canonical] at boundaryStrict
    exact ((not_lt_of_ge (clearance.lower w boundary)) boundaryStrict).elim

/-- The same residual test yields one uniform strict margin from all four
sides of the rational box.

Each side point retains the displayed coordinate on the opposite axis.
The boundary-distance bound excludes a gap no greater than the positive strip width. -/
public theorem residualInteriorMargins
    {p : Dense.Gaussian.Basic.CanonicalCoefficients.CoefficientPolynomial} {box : Box}
    (clearance : Clearance.Box.Boundary.Basic.BoundaryClearance p box) {z : Gaussian.Basic.Canonical}
    (contains : box.Contains z)
    (residualSmall : Data.Gaussian.Norm.Basic.normSq (p.eval z) < clearance.bound / 4) :
    let radius := clearance.residualInteriorRadius
    box.xLower + radius < z.re ∧
      z.re + radius < box.xUpper ∧
      box.yLower + radius < z.im ∧
      z.im + radius < box.yUpper := by
  let radius := clearance.residualInteriorRadius
  have radiusPositive : 0 < radius := by
    simpa only [radius] using clearance.residualInteriorRadius_pos
  have far {w : Gaussian.Basic.Canonical} (boundary : Box.Boundary.OnBoxBoundary box w) :
      radius ^ 2 < Data.Gaussian.Norm.Basic.normSq (w - z) := by
    simpa only [radius] using
      clearance.residualInteriorRadius_sq_lt_normSq_sub contains boundary
        residualSmall
  have left : box.xLower + radius < z.re := by
    match Fraction.Decide.rationalDecLT
        (box.xLower + radius) z.re with
    | isTrue strict => exact strict
    | isFalse strict =>
      have gapLe : z.re - box.xLower ≤ radius := by
        apply Order.Arithmetic.le_of_add_le_add_right_direct
          (c := box.xLower)
        calc
          (z.re - box.xLower) + box.xLower = z.re := by ring1
          _ ≤ box.xLower + radius := le_of_not_gt strict
          _ = radius + box.xLower := by ring1
      have gapNonnegative : 0 ≤ z.re - box.xLower := Order.Arithmetic.sub_nonneg_direct contains.1
      let w : Gaussian.Basic.Canonical := ⟨box.xLower, z.im⟩
      have boundary : Box.Boundary.OnBoxBoundary box w :=
        ⟨⟨le_rfl, box.x_valid, contains.2.2.1, contains.2.2.2⟩,
          Or.inl rfl⟩
      have distanceLe : Data.Gaussian.Norm.Basic.normSq (w - z) ≤ radius ^ 2 := by
        have squareLe := Order.Arithmetic.pow_le_pow_direct
          gapNonnegative gapLe 2
        calc
          Data.Gaussian.Norm.Basic.normSq (w - z) = (z.re - box.xLower) ^ 2 := by
            dsimp only [w, Data.Gaussian.Norm.Basic.normSq, Gaussian.Basic.sub_re, Gaussian.Basic.sub_im]
            ring1
          _ ≤ radius ^ 2 := squareLe
      exact ((not_lt_of_ge distanceLe) (far boundary)).elim
  have right : z.re + radius < box.xUpper := by
    match Fraction.Decide.rationalDecLT
        (z.re + radius) box.xUpper with
    | isTrue strict => exact strict
    | isFalse strict =>
      have gapLe : box.xUpper - z.re ≤ radius := by
        apply Order.Arithmetic.le_of_add_le_add_right_direct
          (c := z.re)
        calc
          (box.xUpper - z.re) + z.re = box.xUpper := by ring1
          _ ≤ z.re + radius := le_of_not_gt strict
          _ = radius + z.re := by ring1
      have gapNonnegative : 0 ≤ box.xUpper - z.re :=
        Order.Arithmetic.sub_nonneg_direct contains.2.1
      let w : Gaussian.Basic.Canonical := ⟨box.xUpper, z.im⟩
      have boundary : Box.Boundary.OnBoxBoundary box w :=
        ⟨⟨box.x_valid, le_rfl, contains.2.2.1, contains.2.2.2⟩,
          Or.inr (Or.inl rfl)⟩
      have distanceLe : Data.Gaussian.Norm.Basic.normSq (w - z) ≤ radius ^ 2 := by
        have squareLe := Order.Arithmetic.pow_le_pow_direct
          gapNonnegative gapLe 2
        calc
          Data.Gaussian.Norm.Basic.normSq (w - z) = (box.xUpper - z.re) ^ 2 := by
            dsimp only [w, Data.Gaussian.Norm.Basic.normSq, Gaussian.Basic.sub_re, Gaussian.Basic.sub_im]
            ring1
          _ ≤ radius ^ 2 := squareLe
      exact ((not_lt_of_ge distanceLe) (far boundary)).elim
  have bottom : box.yLower + radius < z.im := by
    match Fraction.Decide.rationalDecLT
        (box.yLower + radius) z.im with
    | isTrue strict => exact strict
    | isFalse strict =>
      have gapLe : z.im - box.yLower ≤ radius := by
        apply Order.Arithmetic.le_of_add_le_add_right_direct
          (c := box.yLower)
        calc
          (z.im - box.yLower) + box.yLower = z.im := by ring1
          _ ≤ box.yLower + radius := le_of_not_gt strict
          _ = radius + box.yLower := by ring1
      have gapNonnegative : 0 ≤ z.im - box.yLower :=
        Order.Arithmetic.sub_nonneg_direct contains.2.2.1
      let w : Gaussian.Basic.Canonical := ⟨z.re, box.yLower⟩
      have boundary : Box.Boundary.OnBoxBoundary box w :=
        ⟨⟨contains.1, contains.2.1, le_rfl, box.y_valid⟩,
          Or.inr (Or.inr (Or.inl rfl))⟩
      have distanceLe : Data.Gaussian.Norm.Basic.normSq (w - z) ≤ radius ^ 2 := by
        have squareLe := Order.Arithmetic.pow_le_pow_direct
          gapNonnegative gapLe 2
        calc
          Data.Gaussian.Norm.Basic.normSq (w - z) = (z.im - box.yLower) ^ 2 := by
            dsimp only [w, Data.Gaussian.Norm.Basic.normSq, Gaussian.Basic.sub_re, Gaussian.Basic.sub_im]
            ring1
          _ ≤ radius ^ 2 := squareLe
      exact ((not_lt_of_ge distanceLe) (far boundary)).elim
  have top : z.im + radius < box.yUpper := by
    match Fraction.Decide.rationalDecLT
        (z.im + radius) box.yUpper with
    | isTrue strict => exact strict
    | isFalse strict =>
      have gapLe : box.yUpper - z.im ≤ radius := by
        apply Order.Arithmetic.le_of_add_le_add_right_direct
          (c := z.im)
        calc
          (box.yUpper - z.im) + z.im = box.yUpper := by ring1
          _ ≤ z.im + radius := le_of_not_gt strict
          _ = radius + z.im := by ring1
      have gapNonnegative : 0 ≤ box.yUpper - z.im :=
        Order.Arithmetic.sub_nonneg_direct contains.2.2.2
      let w : Gaussian.Basic.Canonical := ⟨z.re, box.yUpper⟩
      have boundary : Box.Boundary.OnBoxBoundary box w :=
        ⟨⟨contains.1, contains.2.1, box.y_valid, le_rfl⟩,
          Or.inr (Or.inr (Or.inr rfl))⟩
      have distanceLe : Data.Gaussian.Norm.Basic.normSq (w - z) ≤ radius ^ 2 := by
        have squareLe := Order.Arithmetic.pow_le_pow_direct
          gapNonnegative gapLe 2
        calc
          Data.Gaussian.Norm.Basic.normSq (w - z) = (box.yUpper - z.im) ^ 2 := by
            dsimp only [w, Data.Gaussian.Norm.Basic.normSq, Gaussian.Basic.sub_re, Gaussian.Basic.sub_im]
            ring1
          _ ≤ radius ^ 2 := squareLe
      exact ((not_lt_of_ge distanceLe) (far boundary)).elim
  exact ⟨left, right, bottom, top⟩

end Purelib.Polynomial.Clearance.Box.Boundary.Basic.BoundaryClearance
