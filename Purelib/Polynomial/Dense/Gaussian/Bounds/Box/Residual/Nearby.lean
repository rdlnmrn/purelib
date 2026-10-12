module

import Purelib.Data.Rat.Fraction
import Purelib.Polynomial.Dense.Gaussian.Bounds.Box
import Purelib.Data.Gaussian.Norm.Basic
import Purelib.Data.Gaussian.Basic
import Purelib.Data.Gaussian.Norm.Bounds
import Purelib.Data.Rat.Fraction.Field
import Purelib.Data.Rat.Fraction.Order.Arithmetic
import Purelib.Geometry.Rational.Box.Basic
import Purelib.Polynomial.Dense.Gaussian.Basic
public import Purelib.Polynomial.Dense.Gaussian.Bounds.Box.Residual
import Mathlib.Algebra.Ring.Defs
import Purelib.Data.Gaussian.Field
import Purelib.Data.Rat.Fraction.Arithmetic
import Purelib.Data.Rat.Fraction.Order.Basic
import Purelib.Geometry.Rational.Box.Refinement
import Purelib.Geometry.Rational.Box.Sample
import Purelib.Polynomial.Dense.Evaluation
import Purelib.Tactic.Ring
meta import Purelib.Elab.ConstructiveInjectivity

open Purelib.Data

open Purelib.Data.Rat

open Purelib.Geometry.Rational

open Purelib.Polynomial

section
@[expose] public section

/-!
# Choice-free local residual extraction

A fixed rational corner of a shrinking box supplies the local sample.  Finite
Horner bounds and the box diagonal bound its residual variation.  If that
sample value were larger than the variation, a finite Rouché contraction to
the nonzero constant path would force raw winding zero.  Thus every proper
nonzero-winding box has an explicitly small rational residual.
-/

namespace Purelib.Polynomial.Dense.Gaussian.Bounds.Box.Residual.Nearby

/-! ## Nearby clear points -/

set_option genInjectivity false in
/-- Finite quantitative data saying that a displayed clear point is close
enough to the fixed anchor of a nonzero-winding box to force constant
dominance. -/
structure NearbyClearPointCertificate
    (p : Polynomial.Dense.Gaussian.Basic.CanonicalCoefficients.CoefficientPolynomial) (ambient small : Box) where
  /-- The displayed Gaussian point whose polynomial residual supplies the clearance. -/ point : Gaussian.Basic.Canonical
  /-- The retained point belongs to the original ambient box. -/ point_mem : ambient.Contains point
  /-- The displayed lower bound for the point's residual quadrance. -/ clearance : Fraction.Rational
  /-- The displayed squared-distance bound from the point to the small box's anchor. -/ radiusSq : Fraction.Rational
  /-- The retained clearance is no larger than the exact residual quadrance. -/ clearance_lower : clearance ≤
    Data.Gaussian.Norm.Basic.normSq (p.eval point)
  /-- The squared distance to the original small-box anchor is bounded by the retained radius. -/ anchor_distance :
    Data.Gaussian.Norm.Basic.normSq (point - small.anchor) ≤ radiusSq
  /-- The retained clearance strictly exceeds twice the combined small-box and nearby-point variation budgets. -/
    dominates :
    2 * (Dense.Gaussian.Bounds.Box.Residual.anchorResidualBound p ambient small +
      Dense.Gaussian.Bounds.Box.denseLipschitzBound p ambient * radiusSq) < clearance

constructive_injectivity NearbyClearPointCertificate

/-- A sufficiently close clear point makes the anchor residual strictly
larger than its whole-box variation. -/
theorem anchorResidualBound_lt_of_nearby_clear_point
    (p : Polynomial.Dense.Gaussian.Basic.CanonicalCoefficients.CoefficientPolynomial) {ambient small : Box}
    (refines : small.Refines ambient)
    (certificate : NearbyClearPointCertificate p ambient small) :
    Dense.Gaussian.Bounds.Box.Residual.anchorResidualBound p ambient small < Data.Gaussian.Norm.Basic.normSq (p.eval
      small.anchor) := by
  have anchorInside : ambient.Contains small.anchor :=
    refines.contains small.contains_anchor
  have variationRaw := Dense.Gaussian.Bounds.Box.normSq_eval_sub_eval_le_denseLipschitzBound
    p certificate.point_mem anchorInside
  have variation : Data.Gaussian.Norm.Basic.normSq (p.eval certificate.point - p.eval small.anchor) ≤
      Dense.Gaussian.Bounds.Box.denseLipschitzBound p ambient * certificate.radiusSq :=
    variationRaw.trans
      (Fraction.Order.Arithmetic.mul_le_mul_of_nonneg_left_direct
        certificate.anchor_distance (Dense.Gaussian.Bounds.Box.denseLipschitzBound_pos p ambient).le)
  have valueIdentity : p.eval certificate.point = p.eval small.anchor +
      (p.eval certificate.point - p.eval small.anchor) := by
    apply Gaussian.Basic.ext <;>
      simp only [Gaussian.Basic.add_re, Gaussian.Basic.add_im, Gaussian.Basic.sub_re, Gaussian.Basic.sub_im] <;>
      ring1
  have valueUpper := Gaussian.Norm.Bounds.normSq_add_le_two (p.eval small.anchor)
    (p.eval certificate.point - p.eval small.anchor)
  rw [← valueIdentity] at valueUpper
  have chain :
      2 * (Dense.Gaussian.Bounds.Box.Residual.anchorResidualBound p ambient small +
          Dense.Gaussian.Bounds.Box.denseLipschitzBound p ambient * certificate.radiusSq) <
        2 * (Data.Gaussian.Norm.Basic.normSq (p.eval small.anchor) +
          Dense.Gaussian.Bounds.Box.denseLipschitzBound p ambient * certificate.radiusSq) := by
    calc
      2 * (Dense.Gaussian.Bounds.Box.Residual.anchorResidualBound p ambient small +
          Dense.Gaussian.Bounds.Box.denseLipschitzBound p ambient * certificate.radiusSq) <
          certificate.clearance := certificate.dominates
      _ ≤ Data.Gaussian.Norm.Basic.normSq (p.eval certificate.point) := certificate.clearance_lower
      _ ≤ 2 * (Data.Gaussian.Norm.Basic.normSq (p.eval small.anchor) +
          Data.Gaussian.Norm.Basic.normSq (p.eval certificate.point - p.eval small.anchor)) :=
        valueUpper
      _ ≤ 2 * (Data.Gaussian.Norm.Basic.normSq (p.eval small.anchor) +
          Dense.Gaussian.Bounds.Box.denseLipschitzBound p ambient * certificate.radiusSq) := by
        have added : Data.Gaussian.Norm.Basic.normSq (p.eval small.anchor) +
              Data.Gaussian.Norm.Basic.normSq (p.eval certificate.point - p.eval small.anchor) ≤
            Data.Gaussian.Norm.Basic.normSq (p.eval small.anchor) +
              Dense.Gaussian.Bounds.Box.denseLipschitzBound p ambient * certificate.radiusSq :=
          add_le_add (le_refl _) variation
        exact Fraction.Order.Arithmetic.mul_le_mul_of_nonneg_left_direct
          added (by decide)
  have cancelledScale :
      Dense.Gaussian.Bounds.Box.Residual.anchorResidualBound p ambient small +
          Dense.Gaussian.Bounds.Box.denseLipschitzBound p ambient * certificate.radiusSq <
        Data.Gaussian.Norm.Basic.normSq (p.eval small.anchor) +
          Dense.Gaussian.Bounds.Box.denseLipschitzBound p ambient * certificate.radiusSq := by
    apply Fraction.Order.Arithmetic.lt_of_mul_lt_mul_right_direct
      (c := 2) ?_ (by decide)
    simpa only [Fraction.Field.mul_comm] using chain
  exact Fraction.Order.Arithmetic.lt_of_add_lt_add_right_direct
    cancelledScale
end Purelib.Polynomial.Dense.Gaussian.Bounds.Box.Residual.Nearby

end
