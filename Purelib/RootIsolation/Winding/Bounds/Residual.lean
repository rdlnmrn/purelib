module
import Purelib.Data.Gaussian.Basic
import Purelib.Data.Gaussian.Norm.Bounds
import Purelib.Data.Rat.Fraction.Order.Arithmetic
import Purelib.Geometry.Rational.Box.Basic
import Purelib.Polynomial.Dense.Gaussian.Basic
public import Purelib.Polynomial.Dense.Gaussian.Bounds.Box.Residual
public import Purelib.Polynomial.Dense.Gaussian.Bounds.Box.Target
import Purelib.Data.Rat.Fraction.Order.Field
import Purelib.Polynomial.Winding.Box.Residual
public import Purelib.RootIsolation.State.WindingOne.Basic
import Purelib.RootIsolation.State.WindingOne.Raw
import Mathlib.Algebra.Ring.Defs
import Purelib.Data.Gaussian.Field
import Purelib.Data.Gaussian.Norm.Basic
import Purelib.Data.Rat.Fraction
import Purelib.Data.Rat.Fraction.Arithmetic
import Purelib.Data.Rat.Fraction.Field
import Purelib.Data.Rat.Fraction.Order.Basic
import Purelib.Geometry.Rational.Box.Bounds
import Purelib.Polynomial.Dense.Basic
import Purelib.Polynomial.Dense.Evaluation
import Purelib.Polynomial.Dense.Gaussian.Bounds.Box
import Purelib.Tactic.Ring

open Purelib.Polynomial.Dense.Gaussian.Bounds

open Purelib.Data.Rat.Fraction.Order

open Purelib.Data.Gaussian.Basic (Canonical)

open Purelib.Data

open Purelib.Geometry.Rational

open Purelib.Polynomial

open Purelib.RootIsolation

section
@[expose] public section

/-!
# Quantitative finite bounds for two coprime polynomials

This module extracts the reusable two-polynomial content of the squarefree
derivative-margin argument.  A displayed Bézout certificate gives an explicit
threshold below which a small value of the left polynomial forces a positive
lower bound for the right polynomial.  Applying the estimate to every point
of a sufficiently refined winding-one box supplies boundary clearance and
zero winding for the other polynomial.
-/

namespace Purelib.RootIsolation.Winding.Bounds.Residual

/-- The squared norm of a Gaussian sum is at most twice the sum of its squared norms. -/
private theorem canonicalNormSqAddLeTwo (left right :
  Canonical) :
    Canonical.normSq (left + right) ≤ 2 * (Canonical.normSq left +
      Canonical.normSq right) := by
  simpa only [Gaussian.Norm.Basic.normSq_eq_canonical] using Gaussian.Norm.Bounds.normSq_add_le_two left right

/-- Every point of a positive-degree winding-one box has squared residual at most four times the ambient Lipschitz bound
and squared diagonal.

The bound combines the retained anchor-residual certificate with finite variation within the same original box. -/
theorem normSq_eval_le_four_lipschitz_diagonal
    {p : Dense.Gaussian.Basic.CanonicalCoefficients.CoefficientPolynomial} {ambient : Box}
    (degreePositive : 0 < p.natDegree)
    (state : State.WindingOne.Basic.WindingOneState p ambient) {z : Canonical}
    (inside : state.box.Contains z) :
    Canonical.normSq (p.eval z) ≤
      4 * Box.denseLipschitzBound p ambient * state.box.diagonalSq := open Purelib.Data.Rat in by
  have anchorResidual :=
    Winding.Box.Residual.anchor_residual_le_of_quadrupledBoxWinding_ne_zero p degreePositive
      state.refinesAmbient state.proper state.raw.rawWinding_ne
  have variation := Box.Residual.normSq_eval_sub_anchor_le p state.refinesAmbient inside
  rw [Gaussian.Norm.Basic.normSq_eq_canonical] at anchorResidual variation
  calc
    Canonical.normSq (p.eval z) =
        Canonical.normSq ((p.eval z - p.eval state.box.anchor) +
          p.eval state.box.anchor) := by
      congr 1
      apply Gaussian.Basic.ext <;>
        simp only [Gaussian.Basic.add_re, Gaussian.Basic.add_im, Gaussian.Basic.sub_re, Gaussian.Basic.sub_im] <;> ring1
    _ ≤ 2 * (Canonical.normSq (p.eval z - p.eval state.box.anchor) +
          Canonical.normSq (p.eval state.box.anchor)) := canonicalNormSqAddLeTwo
            _ _
    _ ≤ 2 * (Box.Residual.anchorResidualBound p ambient state.box +
          Box.Residual.anchorResidualBound p ambient state.box) :=
      Arithmetic.mul_le_mul_of_nonneg_left_direct
        (add_le_add variation anchorResidual) (by decide)
    _ = 4 * Box.denseLipschitzBound p ambient * state.box.diagonalSq := by
      simp only [Box.Residual.anchorResidualBound]
      ring1
end Purelib.RootIsolation.Winding.Bounds.Residual

end

public section

namespace Purelib.RootIsolation.Winding.Bounds.Residual

open Purelib.Data.Rat

/-- A winding-one state meeting the coefficient-derived diagonal budget has uniformly small polynomial residual.

The state's original polynomial, ambient box and positive degree determine
the Lipschitz bound. The positive target computes its sufficient radius;
every point of this actual state then has squared residual below the target.
-/
theorem normSq_eval_lt_of_diagonal
    {p : Dense.Gaussian.Basic.CanonicalCoefficients.CoefficientPolynomial} {ambient : Box}
    (degreePositive : 0 < p.natDegree)
    (state : State.WindingOne.Basic.WindingOneState p ambient)
    {threshold : Fraction.Rational} (thresholdPositive : 0 < threshold)
    (diagonal : state.box.diagonalSq ≤
      Box.Target.uniformResidualRadius p ambient threshold ^ 2)
    {z : Gaussian.Basic.Canonical} (inside : state.box.Contains z) :
    Data.Gaussian.Norm.Basic.normSq (p.eval z) < threshold := by
  let radius := Box.Target.uniformResidualRadius p ambient threshold
  have residual := normSq_eval_le_four_lipschitz_diagonal
    degreePositive state inside
  have radiusSquare := Box.Target.uniformResidualRadius_sq_le p ambient
    thresholdPositive
  have radiusBudget : radius ≤
      threshold / (8 * Box.denseLipschitzBound p ambient) := Fraction.Order.Basic.min_le_right _ _
  have scaled : radius * (8 * Box.denseLipschitzBound p ambient) ≤ threshold :=
    (Fraction.Order.Field.le_div_iff_pos
      (Arithmetic.mul_pos_direct (by decide)
        (Box.denseLipschitzBound_pos p ambient))).mp radiusBudget
  have positiveProduct : 0 < Box.denseLipschitzBound p ambient * radius :=
    Arithmetic.mul_pos_direct
      (Box.denseLipschitzBound_pos p ambient)
      (Box.Target.uniformResidualRadius_pos p ambient thresholdPositive)
  calc
    Data.Gaussian.Norm.Basic.normSq (p.eval z) ≤
        4 * Box.denseLipschitzBound p ambient * state.box.diagonalSq := by simpa only
          [Gaussian.Norm.Basic.normSq_eq_canonical] using residual
    _ ≤ 4 * Box.denseLipschitzBound p ambient * radius ^ 2 :=
      Arithmetic.mul_le_mul_of_nonneg_left_direct diagonal
        (Arithmetic.mul_pos_direct (by decide)
          (Box.denseLipschitzBound_pos p ambient)).le
    _ ≤ 4 * Box.denseLipschitzBound p ambient * radius :=
      Arithmetic.mul_le_mul_of_nonneg_left_direct radiusSquare
        (Arithmetic.mul_pos_direct (by decide)
          (Box.denseLipschitzBound_pos p ambient)).le
    _ < radius * (8 * Box.denseLipschitzBound p ambient) := by
      calc
        4 * Box.denseLipschitzBound p ambient * radius =
            4 * (Box.denseLipschitzBound p ambient * radius) := by ring1
        _ < 8 * (Box.denseLipschitzBound p ambient * radius) :=
          Arithmetic.mul_lt_mul_of_pos_right_direct
            (show (4 : Fraction.Rational) < 8 by decide) positiveProduct
        _ = radius * (8 * Box.denseLipschitzBound p ambient) := by ring1
    _ ≤ threshold := scaled

end Purelib.RootIsolation.Winding.Bounds.Residual

end
