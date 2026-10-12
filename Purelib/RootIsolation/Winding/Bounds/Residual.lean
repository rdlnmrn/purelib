module
import Purelib.Data.Gaussian.Basic
import Purelib.Data.Gaussian.Norm.Bounds
import Purelib.Data.Rat.Fraction.Order.Arithmetic
import Purelib.Geometry.Rational.Box.Basic
import Purelib.Polynomial.Dense.Gaussian.Basic
public import Purelib.Polynomial.Dense.Gaussian.Bounds.Box.Residual
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
      4 * Dense.Gaussian.Bounds.Box.denseLipschitzBound p ambient * state.box.diagonalSq := open Purelib.Data.Rat in by
  have anchorResidual :=
    Winding.Box.Residual.anchor_residual_le_of_quadrupledBoxWinding_ne_zero p degreePositive
      state.refinesAmbient state.proper state.raw.rawWinding_ne
  have variation := Dense.Gaussian.Bounds.Box.Residual.normSq_eval_sub_anchor_le p state.refinesAmbient inside
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
    _ ≤ 2 * (Dense.Gaussian.Bounds.Box.Residual.anchorResidualBound p ambient state.box +
          Dense.Gaussian.Bounds.Box.Residual.anchorResidualBound p ambient state.box) :=
      Fraction.Order.Arithmetic.mul_le_mul_of_nonneg_left_direct
        (add_le_add variation anchorResidual) (by decide)
    _ = 4 * Dense.Gaussian.Bounds.Box.denseLipschitzBound p ambient * state.box.diagonalSq := by
      simp only [Dense.Gaussian.Bounds.Box.Residual.anchorResidualBound]
      ring1
end Purelib.RootIsolation.Winding.Bounds.Residual

end
