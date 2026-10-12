module

import Purelib.Data.Gaussian.Basic
import Purelib.Data.Gaussian.Norm.Basic
import Purelib.Data.Nat.Positive
import Purelib.Data.Rat.Fraction
import Purelib.Data.Rat.Fraction.Order.Arithmetic
import Purelib.Data.Rat.Fraction.Order.Field
import Purelib.Polynomial.Dense.Basic
import Purelib.Polynomial.Dense.Gaussian.Bounds.Box
import Purelib.Polynomial.Dense.Gaussian.Bounds.Box.Residual
import Purelib.Polynomial.Dense.Gaussian.Bounds.RootRadius.Box
import Purelib.Polynomial.Power.Gaussian
public import Purelib.RootIsolation.Power.Isolation.Track
public import Purelib.RootIsolation.Power.Unit.Radius
import Purelib.RootIsolation.State.WindingOne.Basic
import Mathlib.Algebra.Ring.Defs
import Purelib.Data.Rat.Fraction.Arithmetic
import Purelib.Data.Rat.Fraction.Field
import Purelib.Data.Rat.Fraction.Order.Basic
import Purelib.Geometry.Rational.Box.Bounds
import Purelib.RootIsolation.Track.Basic
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

namespace Purelib.RootIsolation.Power.Unit.Source

open Purelib.Data.Gaussian

/-! ## Uniform robust owners on the unit circuit -/

/-- One finite refinement of an independently isolated owner to the common
source scale used by the robust Newton construction. -/
def unitRobustSourceState
    {parameter : Canonical} (parameterNonzero : parameter ≠ 0)
    (parameterUnit : Data.Gaussian.Norm.Basic.normSq parameter = 1)
    (degree : RootDegree) (degreeAtLeastTwo : 2 ≤ degree.value)
    (index : Fin degree.value) :
    State.WindingOne.Basic.WindingOneState (Purelib.Polynomial.Power.Gaussian.rootPolynomial parameter degree)
      (Dense.Gaussian.Bounds.RootRadius.Box.largeSquareBox (Purelib.Polynomial.Power.Gaussian.rootPolynomial parameter
        degree))
        :=
  let track := Power.Isolation.Track.isolatedTrack parameterNonzero degree degreeAtLeastTwo index
  let radius :=
    Power.Unit.Radius.unitRobustSourceRadius parameterUnit degree degreeAtLeastTwo
  track.refine track.initial radius
    (Power.Unit.Radius.unitRobustSourceRadius_pos parameterUnit degree degreeAtLeastTwo)
end Purelib.RootIsolation.Power.Unit.Source

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

namespace Purelib.RootIsolation.Power.Unit.Source

open Purelib.Data.Gaussian

/-- The refined unit-power source box has squared diagonal at most the square of its retained source radius. -/
theorem unitRobustSourceState_diagonalSq_le_radius_sq
    {parameter : Canonical} (parameterNonzero : parameter ≠ 0)
    (parameterUnit : Data.Gaussian.Norm.Basic.normSq parameter = 1)
    (degree : RootDegree) (degreeAtLeastTwo : 2 ≤ degree.value)
    (index : Fin degree.value) :
    (unitRobustSourceState parameterNonzero parameterUnit degree
      degreeAtLeastTwo index).box.diagonalSq ≤
      Power.Unit.Radius.unitRobustSourceRadius parameterUnit degree degreeAtLeastTwo ^ 2 := by
  exact (Power.Isolation.Track.isolatedTrack parameterNonzero degree degreeAtLeastTwo index).accurate
    (Power.Isolation.Track.isolatedTrack parameterNonzero degree degreeAtLeastTwo index).initial
    (Power.Unit.Radius.unitRobustSourceRadius parameterUnit degree degreeAtLeastTwo)
    (Power.Unit.Radius.unitRobustSourceRadius_pos parameterUnit degree degreeAtLeastTwo)
end Purelib.RootIsolation.Power.Unit.Source

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

namespace Purelib.RootIsolation.Power.Unit.Source

open Purelib.Data.Gaussian

/-- The source box's squared diagonal is at most the retained source radius, which is no larger than one. -/
theorem unitRobustSourceState_diagonalSq_le_radius
    {parameter : Canonical} (parameterNonzero : parameter ≠ 0)
    (parameterUnit : Data.Gaussian.Norm.Basic.normSq parameter = 1)
    (degree : RootDegree) (degreeAtLeastTwo : 2 ≤ degree.value)
    (index : Fin degree.value) :
    (unitRobustSourceState parameterNonzero parameterUnit degree
      degreeAtLeastTwo index).box.diagonalSq ≤
      Power.Unit.Radius.unitRobustSourceRadius parameterUnit degree degreeAtLeastTwo := by
  let sourceRadius :=
    Power.Unit.Radius.unitRobustSourceRadius parameterUnit degree degreeAtLeastTwo
  have radiusPositive : 0 < sourceRadius :=
    Power.Unit.Radius.unitRobustSourceRadius_pos parameterUnit degree degreeAtLeastTwo
  have squareLeRadius : sourceRadius ^ 2 ≤ sourceRadius := by
    rw [pow_two]
    calc
      sourceRadius * sourceRadius ≤ 1 * sourceRadius :=
        Fraction.Order.Arithmetic.mul_le_mul_of_nonneg_right_direct
          (Power.Unit.Radius.unitRobustSourceRadius_le_one parameterUnit degree degreeAtLeastTwo)
          radiusPositive.le
      _ = sourceRadius := by ring1
  exact (unitRobustSourceState_diagonalSq_le_radius_sq parameterNonzero
    parameterUnit degree degreeAtLeastTwo index).trans squareLeRadius
end Purelib.RootIsolation.Power.Unit.Source

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

namespace Purelib.RootIsolation.Power.Unit.Source

open Purelib.Data.Gaussian

/-- The source anchor's residual bound satisfies the original one-eighth squared quarter-radius displacement budget. -/
theorem unitRobustSourceState_anchorResidual_le_displacementBudget
    {parameter : Canonical} (parameterNonzero : parameter ≠ 0)
    (parameterUnit : Data.Gaussian.Norm.Basic.normSq parameter = 1)
    (degree : RootDegree) (degreeAtLeastTwo : 2 ≤ degree.value)
    (index : Fin degree.value) :
    Dense.Gaussian.Bounds.Box.Residual.anchorResidualBound (Purelib.Polynomial.Power.Gaussian.rootPolynomial parameter
      degree)
      (Dense.Gaussian.Bounds.RootRadius.Box.largeSquareBox (Purelib.Polynomial.Power.Gaussian.rootPolynomial parameter
        degree))
      (unitRobustSourceState parameterNonzero parameterUnit degree
        degreeAtLeastTwo index).box ≤
      (1 / 8 : Fraction.Rational) *
        (Power.Unit.Radius.unitRobustRadius parameterUnit degree degreeAtLeastTwo / 4) ^ 2 := by
  let p := Purelib.Polynomial.Power.Gaussian.rootPolynomial parameter degree
  let ambient := Dense.Gaussian.Bounds.RootRadius.Box.largeSquareBox p
  let lipschitz := Dense.Gaussian.Bounds.Box.denseLipschitzBound p ambient
  let sourceRadius :=
    Power.Unit.Radius.unitRobustSourceRadius parameterUnit degree degreeAtLeastTwo
  let budget := (1 / 8 : Fraction.Rational) *
    (Power.Unit.Radius.unitRobustRadius parameterUnit degree degreeAtLeastTwo / 4) ^ 2
  have lipschitzPositive : 0 < lipschitz :=
    Dense.Gaussian.Bounds.Box.denseLipschitzBound_pos p ambient
  have scaled : sourceRadius * lipschitz ≤ budget :=
    (Fraction.Order.Field.le_div_iff_pos lipschitzPositive).mp
      (Power.Unit.Radius.unitRobustSourceRadius_le_displacementRatio parameterUnit degree
        degreeAtLeastTwo)
  calc
    Dense.Gaussian.Bounds.Box.Residual.anchorResidualBound p ambient
        (unitRobustSourceState parameterNonzero parameterUnit degree
          degreeAtLeastTwo index).box =
      lipschitz *
        (unitRobustSourceState parameterNonzero parameterUnit degree
          degreeAtLeastTwo index).box.diagonalSq := rfl
    _ ≤ lipschitz * sourceRadius :=
      Fraction.Order.Arithmetic.mul_le_mul_of_nonneg_left_direct
        (unitRobustSourceState_diagonalSq_le_radius parameterNonzero
          parameterUnit degree degreeAtLeastTwo index) lipschitzPositive.le
    _ = sourceRadius * lipschitz := by ring1
    _ ≤ budget := scaled
end Purelib.RootIsolation.Power.Unit.Source

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

namespace Purelib.RootIsolation.Power.Unit.Source

open Purelib.Data.Gaussian

/-- The source anchor's residual bound is at most the original threshold of one quarter. -/
theorem unitRobustSourceState_anchorResidual_le_threshold
    {parameter : Canonical} (parameterNonzero : parameter ≠ 0)
    (parameterUnit : Data.Gaussian.Norm.Basic.normSq parameter = 1)
    (degree : RootDegree) (degreeAtLeastTwo : 2 ≤ degree.value)
    (index : Fin degree.value) :
    Dense.Gaussian.Bounds.Box.Residual.anchorResidualBound (Purelib.Polynomial.Power.Gaussian.rootPolynomial parameter
      degree)
      (Dense.Gaussian.Bounds.RootRadius.Box.largeSquareBox (Purelib.Polynomial.Power.Gaussian.rootPolynomial parameter
        degree))
      (unitRobustSourceState parameterNonzero parameterUnit degree
        degreeAtLeastTwo index).box ≤ (1 / 4 : Fraction.Rational) := by
  let p := Purelib.Polynomial.Power.Gaussian.rootPolynomial parameter degree
  let ambient := Dense.Gaussian.Bounds.RootRadius.Box.largeSquareBox p
  let lipschitz := Dense.Gaussian.Bounds.Box.denseLipschitzBound p ambient
  let sourceRadius :=
    Power.Unit.Radius.unitRobustSourceRadius parameterUnit degree degreeAtLeastTwo
  have lipschitzPositive : 0 < lipschitz :=
    Dense.Gaussian.Bounds.Box.denseLipschitzBound_pos p ambient
  have scaled : sourceRadius * lipschitz ≤ (1 / 4 : Fraction.Rational) :=
    (Fraction.Order.Field.le_div_iff_pos lipschitzPositive).mp
      (Power.Unit.Radius.unitRobustSourceRadius_le_derivativeRatio parameterUnit degree
        degreeAtLeastTwo)
  calc
    Dense.Gaussian.Bounds.Box.Residual.anchorResidualBound p ambient
        (unitRobustSourceState parameterNonzero parameterUnit degree
          degreeAtLeastTwo index).box =
      lipschitz *
        (unitRobustSourceState parameterNonzero parameterUnit degree
          degreeAtLeastTwo index).box.diagonalSq := rfl
    _ ≤ lipschitz * sourceRadius :=
      Fraction.Order.Arithmetic.mul_le_mul_of_nonneg_left_direct
        (unitRobustSourceState_diagonalSq_le_radius parameterNonzero
          parameterUnit degree degreeAtLeastTwo index) lipschitzPositive.le
    _ = sourceRadius * lipschitz := by ring1
    _ ≤ 1 / 4 := scaled
end Purelib.RootIsolation.Power.Unit.Source

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

namespace Purelib.RootIsolation.Power.Unit.Source

open Purelib.Data.Gaussian

/-- The source box's squared diagonal is at most the square of one quarter of the robust radius. -/
theorem unitRobustSourceState_diagonalSq_le_quarterRadius_sq
    {parameter : Canonical} (parameterNonzero : parameter ≠ 0)
    (parameterUnit : Data.Gaussian.Norm.Basic.normSq parameter = 1)
    (degree : RootDegree) (degreeAtLeastTwo : 2 ≤ degree.value)
    (index : Fin degree.value) :
    (unitRobustSourceState parameterNonzero parameterUnit degree
      degreeAtLeastTwo index).box.diagonalSq ≤
      (Power.Unit.Radius.unitRobustRadius parameterUnit degree degreeAtLeastTwo / 4) ^ 2 :=
  (unitRobustSourceState_diagonalSq_le_radius parameterNonzero parameterUnit
    degree degreeAtLeastTwo index).trans
      (Power.Unit.Radius.unitRobustSourceRadius_le_quarterRadius_sq parameterUnit degree
        degreeAtLeastTwo)
end Purelib.RootIsolation.Power.Unit.Source

end
