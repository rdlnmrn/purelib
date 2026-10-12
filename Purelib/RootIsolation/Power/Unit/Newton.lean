module

import Purelib.Data.Gaussian.Basic
import Purelib.Data.Gaussian.Norm.Basic
import all Purelib.Data.Gaussian.Power.Residual.Bounds

import Purelib.Data.Nat.Positive
import Purelib.Data.Rat.Fraction
import Purelib.Data.Rat.Fraction.Cast.Order
import Purelib.Data.Rat.Fraction.Order.Field
import Purelib.Polynomial.Dense.Basic
import Purelib.Polynomial.Dense.Gaussian.Bounds.Box.Residual
import Purelib.Polynomial.Dense.Gaussian.Bounds.RootRadius.Box
import Purelib.Polynomial.Dense.Gaussian.Newton.Box.Anchor
import Purelib.Polynomial.Dense.Gaussian.Newton.Box.Certificate
import Purelib.Polynomial.Power.Gaussian
import Purelib.Polynomial.Power.Gaussian.DerivativeSeparation
import Purelib.Polynomial.Winding.Box.Newton.Prepare
import Purelib.RootIsolation.Power.Unit.Radius
public import Purelib.RootIsolation.Power.Unit.Source
import Mathlib.Algebra.Ring.Defs
import Purelib.Data.Gaussian.Field
import Purelib.Data.Rat.Fraction.Arithmetic
import Purelib.Data.Rat.Fraction.Field
import Purelib.Data.Rat.Fraction.Order.Basic
import Purelib.Geometry.Rational.Box.Basic
import Purelib.Geometry.Rational.Box.Refinement
import Purelib.Geometry.Rational.Box.Sample
import Purelib.Polynomial.Winding.Box.Basic
import Purelib.RootIsolation.State.Raw
import Purelib.RootIsolation.State.WindingOne.Basic
import Purelib.RootIsolation.State.WindingOne.Raw
import Purelib.Tactic.Ring

open Purelib.Data.Gaussian.Basic (Canonical)
open Purelib.Data.Nat.Positive (RootDegree)

open Purelib.Data

open Purelib

open Purelib.Data.Rat

open Purelib.Polynomial

open Purelib.RootIsolation

section
@[expose] public section

/-!
# Finite monodromy for `Z^d - w`

This file specializes finite owner monodromy to the displayed power family.
The first layer records the exact off-zero Bézout identity.  It is uniform in
the displayed positive degree and uses only finite dense-polynomial
calculations:

`-w⁻¹ (Z^d-w) + (w⁻¹ d⁻¹ Z) (Z^d-w)' = 1`.

The later layers use that identity to carry every owner around one explicit
rational circuit of the parameter and to calculate the resulting finite
permutation.
-/

namespace Purelib.RootIsolation.Power.Unit.Newton

open Purelib.Data.Gaussian

/-- The source refinement determines a completely explicit Newton centre.
All hypotheses are discharged by the common unit-parameter estimates rather
than by inspecting an individual owner's boundary clearance. -/
def unitRobustNewton
    {parameter : Canonical} (parameterNonzero : parameter ≠ 0)
    (parameterUnit : Data.Gaussian.Norm.Basic.normSq parameter = 1)
    (degree : RootDegree) (degreeAtLeastTwo : 2 ≤ degree.value)
    (index : Fin degree.value) :
    Dense.Gaussian.Newton.Box.Certificate.SeparatedNewtonCenterCertificate
      (Purelib.Polynomial.Power.Gaussian.rootPolynomial parameter degree)
      (Dense.Gaussian.Bounds.RootRadius.Box.largeSquareBox (Purelib.Polynomial.Power.Gaussian.rootPolynomial parameter
        degree))
      (Power.Unit.Source.unitRobustSourceState parameterNonzero parameterUnit degree
        degreeAtLeastTwo index).box
      (Power.Gaussian.DerivativeSeparation.unitParameterDerivativeSeparation parameterUnit degree degreeAtLeastTwo
        (Dense.Gaussian.Bounds.RootRadius.Box.largeSquareBox
          (Purelib.Polynomial.Power.Gaussian.rootPolynomial parameter degree))) :=
  let source := Power.Unit.Source.unitRobustSourceState parameterNonzero parameterUnit degree
    degreeAtLeastTwo index
  Winding.Box.Newton.Prepare.computeNewtonCenterOfRawWindingSeparated
    (Purelib.Polynomial.Power.Gaussian.rootPolynomial parameter degree)
    (by rw [Purelib.Polynomial.Power.Gaussian.rootPolynomial_degree]; exact degree.positive)
    (Power.Gaussian.DerivativeSeparation.unitParameterDerivativeSeparation parameterUnit degree degreeAtLeastTwo _)
    source.refinesAmbient source.proper source.raw.rawWinding_ne
    (Power.Unit.Source.unitRobustSourceState_anchorResidual_le_threshold parameterNonzero
      parameterUnit degree degreeAtLeastTwo index)
end Purelib.RootIsolation.Power.Unit.Newton

end

section
@[expose] public section

/-!
# Finite monodromy for `Z^d - w`

This file specializes finite owner monodromy to the displayed power family.
The first layer records the exact off-zero Bézout identity.  It is uniform in
the displayed positive degree and uses only finite dense-polynomial
calculations:

`-w⁻¹ (Z^d-w) + (w⁻¹ d⁻¹ Z) (Z^d-w)' = 1`.

The later layers use that identity to carry every owner around one explicit
rational circuit of the parameter and to calculate the resulting finite
permutation.
-/

namespace Purelib.RootIsolation.Power.Unit.Newton

open Purelib.Data.Gaussian

/-- The Newton correction is at most one quarter of the robust radius in
squared norm. -/
theorem unitRobustNewton_displacement_le_quarterRadius_sq
    {parameter : Canonical} (parameterNonzero : parameter ≠ 0)
    (parameterUnit : Data.Gaussian.Norm.Basic.normSq parameter = 1)
    (degree : RootDegree) (degreeAtLeastTwo : 2 ≤ degree.value)
    (index : Fin degree.value) :
    Data.Gaussian.Norm.Basic.normSq
        ((unitRobustNewton parameterNonzero parameterUnit degree
            degreeAtLeastTwo index).point -
          (Power.Unit.Source.unitRobustSourceState parameterNonzero parameterUnit degree
            degreeAtLeastTwo index).box.anchor) ≤
      (Power.Unit.Radius.unitRobustRadius parameterUnit degree degreeAtLeastTwo / 4) ^ 2 := by
  let p := Purelib.Polynomial.Power.Gaussian.rootPolynomial parameter degree
  let ambient := Dense.Gaussian.Bounds.RootRadius.Box.largeSquareBox p
  let source := Power.Unit.Source.unitRobustSourceState parameterNonzero parameterUnit degree
    degreeAtLeastTwo index
  let separation := Power.Gaussian.DerivativeSeparation.unitParameterDerivativeSeparation parameterUnit degree
    degreeAtLeastTwo ambient
  let newton := unitRobustNewton parameterNonzero parameterUnit degree
    degreeAtLeastTwo index
  let q := Power.Unit.Radius.unitRobustRadius parameterUnit degree degreeAtLeastTwo / 4
  have budget :=
    Power.Unit.Source.unitRobustSourceState_anchorResidual_le_displacementBudget
      parameterNonzero parameterUnit degree degreeAtLeastTwo index
  have marginPositive : 0 < separation.margin := separation.margin_pos
  calc
    Data.Gaussian.Norm.Basic.normSq (newton.point - source.box.anchor) =
        Data.Gaussian.Norm.Basic.normSq (Dense.Gaussian.Newton.Box.Anchor.anchorNewtonCenter p source.box -
          source.box.anchor) := by rw [newton.point_eq]
    _ ≤ Dense.Gaussian.Bounds.Box.Residual.anchorResidualBound p ambient source.box /
          separation.margin := newton.displacementMargin
    _ ≤ q ^ 2 :=
      (Fraction.Order.Field.div_le_iff_pos marginPositive).mpr (by
        calc
          Dense.Gaussian.Bounds.Box.Residual.anchorResidualBound p ambient source.box ≤
              separation.margin * q ^ 2 := by
            simpa only [separation, Power.Gaussian.DerivativeSeparation.unitParameterDerivativeSeparation, q] using
              budget
          _ = q ^ 2 * separation.margin := by ring1)
end Purelib.RootIsolation.Power.Unit.Newton

end

section
@[expose] public section

/-!
# Finite monodromy for `Z^d - w`

This file specializes finite owner monodromy to the displayed power family.
The first layer records the exact off-zero Bézout identity.  It is uniform in
the displayed positive degree and uses only finite dense-polynomial
calculations:

`-w⁻¹ (Z^d-w) + (w⁻¹ d⁻¹ Z) (Z^d-w)' = 1`.

The later layers use that identity to carry every owner around one explicit
rational circuit of the parameter and to calculate the resulting finite
permutation.
-/

namespace Purelib.RootIsolation.Power.Unit.Newton

open Purelib.Data.Gaussian

/-- Dividing the already small robust radius by four gives the coordinate
budget used to place the Newton centre. -/
theorem unitRobustQuarterRadius_le_quarter
    {parameter : Canonical} (parameterUnit : Data.Gaussian.Norm.Basic.normSq parameter = 1)
    (degree : RootDegree) (degreeAtLeastTwo : 2 ≤ degree.value) :
    Power.Unit.Radius.unitRobustRadius parameterUnit degree degreeAtLeastTwo / 4 ≤
      (1 / 4 : Fraction.Rational) := by
  apply (Fraction.Order.Field.div_le_iff_pos
    (show (0 : Fraction.Rational) < 4 by
      exact Fraction.Cast.Order.natCast_pos_direct (by decide))).mpr
  calc
    Power.Unit.Radius.unitRobustRadius parameterUnit degree degreeAtLeastTwo ≤
        (1 / 8 : Fraction.Rational) :=
      Power.Unit.Radius.unitRobustRadius_le_eighth parameterUnit degree degreeAtLeastTwo
    _ ≤ 1 := by decide
    _ = (1 / 4 : Fraction.Rational) * 4 := by decide
end Purelib.RootIsolation.Power.Unit.Newton

end

section
@[expose] public section

/-!
# Finite monodromy for `Z^d - w`

This file specializes finite owner monodromy to the displayed power family.
The first layer records the exact off-zero Bézout identity.  It is uniform in
the displayed positive degree and uses only finite dense-polynomial
calculations:

`-w⁻¹ (Z^d-w) + (w⁻¹ d⁻¹ Z) (Z^d-w)' = 1`.

The later layers use that identity to carry every owner around one explicit
rational circuit of the parameter and to calculate the resulting finite
permutation.
-/

namespace Purelib.RootIsolation.Power.Unit.Newton

open Purelib.Data.Gaussian

/-- The anchor selected by every common source refinement lies in the same
coarse rational radial envelope. -/
theorem unitRobustSourceState_anchor_normSq_le
    {parameter : Canonical} (parameterNonzero : parameter ≠ 0)
    (parameterUnit : Data.Gaussian.Norm.Basic.normSq parameter = 1)
    (degree : RootDegree) (degreeAtLeastTwo : 2 ≤ degree.value)
    (index : Fin degree.value) :
    Data.Gaussian.Norm.Basic.normSq
        (Power.Unit.Source.unitRobustSourceState parameterNonzero parameterUnit degree
          degreeAtLeastTwo index).box.anchor ≤ (5 / 2 : Fraction.Rational) := by
  let source := Power.Unit.Source.unitRobustSourceState parameterNonzero parameterUnit degree
    degreeAtLeastTwo index
  let newton := unitRobustNewton parameterNonzero parameterUnit degree
    degreeAtLeastTwo index
  have residualSmall :
      Data.Gaussian.Norm.Basic.normSq (source.box.anchor ^ degree.value - parameter) ≤
        (1 / 4 : Fraction.Rational) := by
    rw [← Purelib.Polynomial.Power.Gaussian.rootPolynomial_eval parameter source.box.anchor degree]
    exact newton.residual.trans
      (Power.Unit.Source.unitRobustSourceState_anchorResidual_le_threshold parameterNonzero
        parameterUnit degree degreeAtLeastTwo index)
  exact Gaussian.Power.Residual.Bounds.normSq_le_five_halves_of_power_residual degree.positive parameterUnit
    residualSmall
end Purelib.RootIsolation.Power.Unit.Newton

end
