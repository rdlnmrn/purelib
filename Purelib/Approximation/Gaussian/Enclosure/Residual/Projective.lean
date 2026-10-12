module
import Purelib.Approximation.Gaussian.Enclosure.Ball.Basic
import Purelib.Approximation.Gaussian.Enclosure.Residual
public import Purelib.Data.CCL.Encoding.Padding.Residual
import Purelib.Data.Gaussian.Basic
import Purelib.Data.Gaussian.Constants
import Purelib.Data.Gaussian.Field
import Purelib.Geometry.Projective.Chordal.DyadicTail
import Purelib.Geometry.Projective.Line.Basic

import Purelib.Tactic.QuotientFreeOmega

open Purelib.Data.Gaussian.Basic (Canonical)

open Purelib

open Purelib.Approximation.Gaussian.Enclosure

open Purelib.Data.CCL.Encoding.Padding

open Purelib.Geometry.Projective

open Purelib.Geometry.Projective.Chordal.DyadicTail

open Purelib.Geometry.Projective.Line

section
@[expose] public section

/-!
# Optional contraction accounting for progressive arithmetic cursors

The canonical encoder, raw parser, and progressive `List Bool` cursor do not
carry an error symbol.  This module is a separate proof sidecar.  It packages
neutral chart changes and normalized sector emissions into finite traces of
projectively coherent redundant blocks, then combines their dyadic
contraction with the explicit coefficient of any already committed decoder
prefix.
-/

namespace Purelib.Approximation.Gaussian.Enclosure.Residual.Projective

/-! ## Terminal unary accuracy -/

/-- The residual decision's affine-or-`omega` witness is exactly the homogeneous residual tail used by the machine. -/
theorem loopTailOfSmall_point_equivalent_homogeneous
    {count : Nat} {ball : Approximation.Gaussian.Enclosure.Ball}
    (small : Residual.SmallBall ball
      (Residual.paddingTarget count))
    (residual : Canonical) (inside : ball.Contains residual) :
    (Purelib.Data.CCL.Encoding.Padding.Residual.loopTailOfSmall
      small residual inside).point.Equivalent ⟨1, Canonical.gamma * residual⟩ := by
  unfold Residual.loopTailOfSmall
  split
  · rename_i residualZero
    simp only [LoopTail.point,
      Line.Proj.omega, Proj.Equivalent]
    rw [residualZero, Data.Gaussian.Basic.mul_zero]
  · rename_i residualNonzero
    let product := Canonical.gamma * residual
    have productNonzero : product ≠ 0 :=
      Data.Gaussian.Field.mul_ne_zero_direct (by decide) residualNonzero
    simp only [LoopTail.point,
      Line.Proj.affine, Proj.Equivalent]
    change product⁻¹ * product = 1 * 1
    rw [Data.Gaussian.Basic.mul_one]
    exact Canonical.inv_mul_cancel
      product productNonzero
end Purelib.Approximation.Gaussian.Enclosure.Residual.Projective

end
