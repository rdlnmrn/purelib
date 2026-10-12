module

import Purelib.Data.Gaussian.Basic
import Purelib.Data.Gaussian.Norm.Basic
import Purelib.Data.Nat.Positive
import Purelib.Geometry.Rational.Box.Square.Centered
import Purelib.Polynomial.Clearance.Box.Boundary.Basic
public import Purelib.Polynomial.Clearance.Box.Boundary.Newton.Square.Separated
import Purelib.Polynomial.Dense.Basic
import Purelib.Polynomial.Dense.Gaussian.Bounds.Box.Taylor
import Purelib.Polynomial.Dense.Gaussian.Bounds.RootRadius.Box
import Purelib.Polynomial.Dense.Gaussian.Newton.Box.Anchor
import Purelib.Polynomial.Dense.Gaussian.Newton.Box.Square.Bounds
import Purelib.Polynomial.Dense.Gaussian.Newton.Box.Square.Separated
import Purelib.Polynomial.Power.Gaussian
import Purelib.Polynomial.Power.Gaussian.DerivativeSeparation
import Purelib.RootIsolation.Power.Bounds
public import Purelib.RootIsolation.Power.Unit.Box
import Purelib.RootIsolation.Power.Unit.Newton
import Purelib.RootIsolation.Power.Unit.Radius
import Purelib.RootIsolation.Power.Unit.Source
import Mathlib.Algebra.Ring.Defs
import Mathlib.Order.Defs.PartialOrder
import Purelib.Data.Gaussian.Field
import Purelib.Data.Rat.Fraction
import Purelib.Data.Rat.Fraction.Arithmetic
import Purelib.Data.Rat.Fraction.Field
import Purelib.Data.Rat.Fraction.Order.Basic
import Purelib.Geometry.Rational.Box.Basic
import Purelib.Geometry.Rational.Box.Refinement
import Purelib.Geometry.Rational.Box.Sample
import Purelib.Polynomial.Dense.Gaussian.Derivative.Separation.Basic
import Purelib.Polynomial.Dense.Gaussian.Newton.Box.Certificate
import Purelib.RootIsolation.State.WindingOne.Basic

open Purelib.Data.Gaussian.Basic (Canonical)
open Purelib.Data.Nat.Positive (RootDegree)

open Purelib.Data.Gaussian.Norm.Basic (normSq)

open Purelib.Data

open Purelib

open Purelib.Data.Rat

open Purelib.Geometry.Rational

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

namespace Purelib.RootIsolation.Power.Unit.Clearance

open Purelib.Data.Gaussian

/-- The exact Gaussian parameter one used to evaluate the common unit-circle clearance budget. -/
def unitReferenceParameter : Canonical := 1
end Purelib.RootIsolation.Power.Unit.Clearance

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

namespace Purelib.RootIsolation.Power.Unit.Clearance

open Purelib.Data.Gaussian

/-- The retained reference parameter is nonzero. -/
theorem unitReferenceParameter_nonzero :
  unitReferenceParameter ≠ 0 := by
  decide
end Purelib.RootIsolation.Power.Unit.Clearance

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

namespace Purelib.RootIsolation.Power.Unit.Clearance

open Purelib.Data.Gaussian

/-- The retained reference parameter has quadrance one. -/
theorem unitReferenceParameter_unit : normSq
  unitReferenceParameter = 1 :=
  Gaussian.Norm.Basic.normSq_one
end Purelib.RootIsolation.Power.Unit.Clearance

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

namespace Purelib.RootIsolation.Power.Unit.Clearance

open Purelib.Data.Gaussian

/-- The coefficient-computed positive boundary clearance of a robust owner. -/
def unitRobustBoundaryClearance
    {parameter : Canonical} (parameterNonzero : parameter ≠ 0)
    (parameterUnit : normSq parameter = 1)
    (degree : RootDegree) (degreeAtLeastTwo : 2 ≤ degree.value)
    (index : Fin degree.value) :
    Clearance.Box.Boundary.Basic.BoundaryClearance (Purelib.Polynomial.Power.Gaussian.rootPolynomial parameter degree)
      (Power.Unit.Box.unitRobustBox parameterNonzero parameterUnit degree degreeAtLeastTwo
        index) := by
  let p := Purelib.Polynomial.Power.Gaussian.rootPolynomial parameter degree
  let ambient := Dense.Gaussian.Bounds.RootRadius.Box.largeSquareBox p
  let source := Power.Unit.Source.unitRobustSourceState parameterNonzero parameterUnit degree
    degreeAtLeastTwo index
  let separation := Power.Gaussian.DerivativeSeparation.unitParameterDerivativeSeparation parameterUnit degree
    degreeAtLeastTwo ambient
  let newton := Power.Unit.Newton.unitRobustNewton parameterNonzero parameterUnit degree
    degreeAtLeastTwo index
  let r := Power.Unit.Radius.unitRobustRadius parameterUnit degree degreeAtLeastTwo
  have degreeTwo : 2 ≤ p.natDegree := by
    rw [Purelib.Polynomial.Power.Gaussian.rootPolynomial_degree]
    exact degreeAtLeastTwo
  have targetRefines :
      (Box.Square.Centered.Affine.centeredSquare
        (Dense.Gaussian.Newton.Box.Anchor.anchorNewtonCenter p source.box) r
        (Power.Unit.Radius.unitRobustRadius_pos parameterUnit degree degreeAtLeastTwo).le).Refines
          ambient := by
    rw [← Power.Unit.Box.unitRobustBox_eq_centeredNewtonSquare parameterNonzero parameterUnit
      degree degreeAtLeastTwo index]
    exact Power.Unit.Box.unitRobustBox_refinesAmbient parameterNonzero parameterUnit degree
      degreeAtLeastTwo index
  have displacement :
      normSq (Dense.Gaussian.Newton.Box.Anchor.anchorNewtonCenter p source.box -
        source.box.anchor) ≤ r ^ 2 := by
    rw [← newton.point_eq]
    exact Power.Unit.Box.unitRobustNewton_displacement_le_radius_sq parameterNonzero
      parameterUnit degree degreeAtLeastTwo index
  have taylor :
      2 * (36 * Dense.Gaussian.Bounds.Box.Taylor.denseTaylorRemainderBound p ambient *
        r ^ 2) ≤ separation.margin := by
    simpa only [separation, Power.Gaussian.DerivativeSeparation.unitParameterDerivativeSeparation] using
      Power.Unit.Radius.unitRobustRadius_taylor parameterUnit degree degreeAtLeastTwo
  rw [Power.Unit.Box.unitRobustBox_eq_centeredNewtonSquare parameterNonzero parameterUnit
    degree degreeAtLeastTwo index]
  exact Clearance.Box.Boundary.Newton.Square.Separated.separatedNewtonSquareBoundaryClearance degreeTwo
    newton source.refinesAmbient
    (Power.Unit.Radius.unitRobustRadius_pos parameterUnit degree degreeAtLeastTwo)
    targetRefines displacement taylor
end Purelib.RootIsolation.Power.Unit.Clearance

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

namespace Purelib.RootIsolation.Power.Unit.Clearance

open Purelib.Data.Gaussian

/-- The robust boundary certificate retains exactly the squared dominance margin divided by four times the linearization
majorant. -/
theorem unitRobustBoundaryClearance_bound
    {parameter : Canonical} (parameterNonzero : parameter ≠ 0)
    (parameterUnit : normSq parameter = 1)
    (degree : RootDegree) (degreeAtLeastTwo : 2 ≤ degree.value)
    (index : Fin degree.value) :
    (unitRobustBoundaryClearance parameterNonzero parameterUnit degree
      degreeAtLeastTwo index).bound =
      let p := Purelib.Polynomial.Power.Gaussian.rootPolynomial parameter degree
      let ambient := Dense.Gaussian.Bounds.RootRadius.Box.largeSquareBox p
      let separation := Power.Gaussian.DerivativeSeparation.unitParameterDerivativeSeparation parameterUnit degree
        degreeAtLeastTwo ambient
      let r := Power.Unit.Radius.unitRobustRadius parameterUnit degree degreeAtLeastTwo
      Dense.Gaussian.Newton.Box.Square.Separated.separatedNewtonDominanceMargin separation r ^ 2 /
        (4 * Dense.Gaussian.Newton.Box.Square.Bounds.separatedNewtonLinearizationMajorant
          p ambient r) := by
  unfold unitRobustBoundaryClearance
  rfl
end Purelib.RootIsolation.Power.Unit.Clearance

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

namespace Purelib.RootIsolation.Power.Unit.Clearance

open Purelib.Data.Gaussian

/-- The common boundary budget expression for every robust owner at one unit
parameter.  It contains only finite coefficient majorants and the fixed
rational radius. -/
def unitRobustClearanceScale
    {parameter : Canonical} (parameterUnit : normSq parameter = 1)
    (degree : RootDegree) (degreeAtLeastTwo : 2 ≤ degree.value) : Fraction.Rational :=
  let p := Purelib.Polynomial.Power.Gaussian.rootPolynomial parameter degree
  let ambient := Dense.Gaussian.Bounds.RootRadius.Box.largeSquareBox p
  let separation := Power.Gaussian.DerivativeSeparation.unitParameterDerivativeSeparation parameterUnit degree
    degreeAtLeastTwo ambient
  let r := Power.Unit.Radius.unitRobustRadius parameterUnit degree degreeAtLeastTwo
  Dense.Gaussian.Newton.Box.Square.Separated.separatedNewtonDominanceMargin separation r ^ 2 /
    (4 * Dense.Gaussian.Newton.Box.Square.Bounds.separatedNewtonLinearizationMajorant p ambient r)
end Purelib.RootIsolation.Power.Unit.Clearance

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

namespace Purelib.RootIsolation.Power.Unit.Clearance

open Purelib.Data.Gaussian

/-- One parameter-free positive rational budget shared by all robust boxes on
the unit circuit. -/
def uniformRobustClearance (degree : RootDegree)
    (degreeAtLeastTwo : 2 ≤ degree.value) : Fraction.Rational :=
  unitRobustClearanceScale unitReferenceParameter_unit degree degreeAtLeastTwo
end Purelib.RootIsolation.Power.Unit.Clearance

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

namespace Purelib.RootIsolation.Power.Unit.Clearance

open Purelib.Data.Gaussian

/-- The robust boundary certificate's bound equals the coefficient-derived clearance scale. -/
theorem unitRobustBoundaryClearance_bound_eq_scale
    {parameter : Canonical} (parameterNonzero : parameter ≠ 0)
    (parameterUnit : normSq parameter = 1)
    (degree : RootDegree) (degreeAtLeastTwo : 2 ≤ degree.value)
    (index : Fin degree.value) :
    (unitRobustBoundaryClearance parameterNonzero parameterUnit degree
      degreeAtLeastTwo index).bound =
        unitRobustClearanceScale parameterUnit degree degreeAtLeastTwo := by
  exact unitRobustBoundaryClearance_bound parameterNonzero parameterUnit degree
    degreeAtLeastTwo index
end Purelib.RootIsolation.Power.Unit.Clearance

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

namespace Purelib.RootIsolation.Power.Unit.Clearance

open Purelib.Data.Gaussian

/-- The common clearance budget for all unit-parameter robust boxes is positive. -/
theorem uniformRobustClearance_pos (degree :
  RootDegree)
    (degreeAtLeastTwo : 2 ≤ degree.value) :
    0 < uniformRobustClearance degree degreeAtLeastTwo := by
  let index : Fin degree.value := ⟨0, degree.positive⟩
  have positive :=
    (unitRobustBoundaryClearance unitReferenceParameter_nonzero
      unitReferenceParameter_unit degree degreeAtLeastTwo index).positive
  rw [unitRobustBoundaryClearance_bound_eq_scale] at positive
  exact positive
end Purelib.RootIsolation.Power.Unit.Clearance

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

namespace Purelib.RootIsolation.Power.Unit.Clearance

open Purelib.Data.Gaussian

/-- The common clearance scale depends on a unit parameter only through its
quadrance. -/
theorem unitRobustClearanceScale_eq_of_normSq_eq
    {source target : Canonical}
    (sourceUnit : normSq source = 1) (targetUnit : normSq target = 1)
    (equalNorm : normSq source = normSq target)
    (degree : RootDegree) (degreeAtLeastTwo : 2 ≤ degree.value) :
    unitRobustClearanceScale sourceUnit degree degreeAtLeastTwo =
      unitRobustClearanceScale targetUnit degree degreeAtLeastTwo := by
  unfold unitRobustClearanceScale
    Dense.Gaussian.Newton.Box.Square.Separated.separatedNewtonDominanceMargin
    Dense.Gaussian.Newton.Box.Square.Bounds.newtonErrorBudget
    Dense.Gaussian.Newton.Box.Square.Bounds.separatedNewtonLinearizationMajorant
  dsimp only [Power.Gaussian.DerivativeSeparation.unitParameterDerivativeSeparation]
  rw [Power.Unit.Radius.unitRobustRadius_eq_of_normSq_eq sourceUnit targetUnit equalNorm degree
      degreeAtLeastTwo,
    Power.Bounds.denseTaylorRemainderBound_polynomial_eq_of_normSq_eq equalNorm degree,
    Power.Gaussian.derivative_polynomial_eq source target degree,
    Power.Bounds.largeSquareBox_polynomial_eq_of_normSq_eq equalNorm degree]
end Purelib.RootIsolation.Power.Unit.Clearance

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

namespace Purelib.RootIsolation.Power.Unit.Clearance

open Purelib.Data.Gaussian

/-- Every retained robust unit-parameter box has exactly the same parameter-independent clearance bound. -/
theorem unitRobustBoundaryClearance_uniform
    {parameter : Canonical} (parameterNonzero : parameter ≠ 0)
    (parameterUnit : normSq parameter = 1)
    (degree : RootDegree) (degreeAtLeastTwo : 2 ≤ degree.value)
    (index : Fin degree.value) :
    (unitRobustBoundaryClearance parameterNonzero parameterUnit degree
      degreeAtLeastTwo index).bound =
        uniformRobustClearance degree degreeAtLeastTwo := by
  rw [unitRobustBoundaryClearance_bound_eq_scale]
  exact unitRobustClearanceScale_eq_of_normSq_eq parameterUnit
    unitReferenceParameter_unit
    (parameterUnit.trans unitReferenceParameter_unit.symm) degree
    degreeAtLeastTwo
end Purelib.RootIsolation.Power.Unit.Clearance

end
