module

import Purelib.Data.Gaussian.Basic
import Purelib.Data.Nat.Positive
import Purelib.Geometry.Gaussian.UnitCircle.Quarter
import Purelib.Geometry.Gaussian.UnitCircle.Stereographic
import Purelib.Polynomial.Dense.Basic
import Purelib.RootIsolation.Power.Unit.Chain.Basic
public import Purelib.RootIsolation.Power.Unit.Chain.Rotation
import Purelib.RootIsolation.Power.Unit.Circuit.Clearance
public import Purelib.RootIsolation.Power.Unit.Circuit.Join
import Purelib.RootIsolation.Power.Unit.Circuit.Point
import Purelib.RootIsolation.Power.Unit.Circuit.Product
import Purelib.RootIsolation.Power.Unit.Circuit.Subdivision
public import Purelib.RootIsolation.Power.Unit.Circuit.Vertex
import Purelib.RootIsolation.Power.Unit.Move.Budget
import Mathlib.Algebra.Ring.Defs
import Mathlib.Order.Basic
import Purelib.Data.Gaussian.Norm.Basic
import Purelib.Data.Rat.Fraction
import Purelib.Data.Rat.Fraction.Arithmetic
import Purelib.Data.Rat.Fraction.Field
import Purelib.Data.Rat.Fraction.Order.Basic
import Purelib.Geometry.Gaussian.UnitCircle.Basic
import Purelib.Tactic.QuotientFreeOmega

open Purelib.Data

open Purelib

open Purelib.RootIsolation

section
public section

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

namespace Purelib.RootIsolation.Power.Unit.Circuit.Chain

open Purelib.Data.Gaussian

/-- Join the first and second quarter endpoints using their exact equality of unit values. -/
@[expose] def unitCircuitFirstSecondJoin (degree : Data.Nat.Positive.RootDegree)
    (degreeAtLeastTwo : 2 ≤ degree.value) :
    Power.Unit.Chain.Basic.UnitChain degree degreeAtLeastTwo
      (Power.Unit.Circuit.Vertex.unitCircuitVertex .first degree degreeAtLeastTwo
        (Power.Unit.Circuit.Subdivision.unitCircuitStepCount degree degreeAtLeastTwo))
      (Power.Unit.Circuit.Vertex.unitCircuitVertex .second degree degreeAtLeastTwo 0) :=
  Power.Unit.Chain.Basic.UnitChain.equalValue (Power.Unit.Circuit.Join.unitCircuitQuarters_join degree
    degreeAtLeastTwo).1
end Purelib.RootIsolation.Power.Unit.Circuit.Chain

end

section
public section

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

namespace Purelib.RootIsolation.Power.Unit.Circuit.Chain

open Purelib.Data.Gaussian

/-- Close the fourth quarter back to the first using their exact equality of unit values. -/
@[expose] def unitCircuitFourthFirstJoin (degree : Data.Nat.Positive.RootDegree)
    (degreeAtLeastTwo : 2 ≤ degree.value) :
    Power.Unit.Chain.Basic.UnitChain degree degreeAtLeastTwo
      (Power.Unit.Circuit.Vertex.unitCircuitVertex .fourth degree degreeAtLeastTwo
        (Power.Unit.Circuit.Subdivision.unitCircuitStepCount degree degreeAtLeastTwo))
      (Power.Unit.Circuit.Vertex.unitCircuitVertex .first degree degreeAtLeastTwo 0) :=
  Power.Unit.Chain.Basic.UnitChain.equalValue (Power.Unit.Circuit.Join.unitCircuitQuarters_join degree
    degreeAtLeastTwo).2.2.2
end Purelib.RootIsolation.Power.Unit.Circuit.Chain

end

section
public section

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

namespace Purelib.RootIsolation.Power.Unit.Circuit.Chain

open Purelib.Data.Gaussian

/-- Join the second and third quarter endpoints using their exact equality of unit values. -/
@[expose] def unitCircuitSecondThirdJoin (degree : Data.Nat.Positive.RootDegree)
    (degreeAtLeastTwo : 2 ≤ degree.value) :
    Power.Unit.Chain.Basic.UnitChain degree degreeAtLeastTwo
      (Power.Unit.Circuit.Vertex.unitCircuitVertex .second degree degreeAtLeastTwo
        (Power.Unit.Circuit.Subdivision.unitCircuitStepCount degree degreeAtLeastTwo))
      (Power.Unit.Circuit.Vertex.unitCircuitVertex .third degree degreeAtLeastTwo 0) :=
  Power.Unit.Chain.Basic.UnitChain.equalValue (Power.Unit.Circuit.Join.unitCircuitQuarters_join degree
    degreeAtLeastTwo).2.1
end Purelib.RootIsolation.Power.Unit.Circuit.Chain

end

section
public section

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

namespace Purelib.RootIsolation.Power.Unit.Circuit.Chain

open Purelib.Data.Gaussian

/-- Join the third and fourth quarter endpoints using their exact equality of unit values. -/
@[expose] def unitCircuitThirdFourthJoin (degree : Data.Nat.Positive.RootDegree)
    (degreeAtLeastTwo : 2 ≤ degree.value) :
    Power.Unit.Chain.Basic.UnitChain degree degreeAtLeastTwo
      (Power.Unit.Circuit.Vertex.unitCircuitVertex .third degree degreeAtLeastTwo
        (Power.Unit.Circuit.Subdivision.unitCircuitStepCount degree degreeAtLeastTwo))
      (Power.Unit.Circuit.Vertex.unitCircuitVertex .fourth degree degreeAtLeastTwo 0) :=
  Power.Unit.Chain.Basic.UnitChain.equalValue (Power.Unit.Circuit.Join.unitCircuitQuarters_join degree
    degreeAtLeastTwo).2.2.1
end Purelib.RootIsolation.Power.Unit.Circuit.Chain

end

section
public section

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

namespace Purelib.RootIsolation.Power.Unit.Circuit.Chain

open Purelib.Data.Gaussian

/-- The last subdivided vertex has the exact terminal stereographic quarter value. -/
theorem unitCircuitVertex_last_value
    (quarter : Geometry.Gaussian.UnitCircle.Quarter.UnitCircuitQuarter) (degree : Data.Nat.Positive.RootDegree)
    (degreeAtLeastTwo : 2 ≤ degree.value) :
    (Power.Unit.Circuit.Vertex.unitCircuitVertex quarter degree degreeAtLeastTwo
      (Power.Unit.Circuit.Subdivision.unitCircuitStepCount degree degreeAtLeastTwo)).value =
      Geometry.Gaussian.UnitCircle.Quarter.unitCircuitMultiplier quarter * ⟨0, 1⟩ := by
  simp only [-eq_self, -iff_self, Power.Unit.Circuit.Vertex.unitCircuitVertex,
    Power.Unit.Circuit.Point.unitCircuitPoint,
    Power.Unit.Circuit.Subdivision.unitCircuitParameter_last,
      Geometry.Gaussian.UnitCircle.Stereographic.unitQuarterPoint_one]
  rfl
end Purelib.RootIsolation.Power.Unit.Circuit.Chain

end

section
public section

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

namespace Purelib.RootIsolation.Power.Unit.Circuit.Chain

open Purelib.Data.Gaussian

/-- The first subdivided vertex has the exact initial stereographic quarter value. -/
theorem unitCircuitVertex_zero_value
    (quarter : Geometry.Gaussian.UnitCircle.Quarter.UnitCircuitQuarter) (degree : Data.Nat.Positive.RootDegree)
    (degreeAtLeastTwo : 2 ≤ degree.value) :
    (Power.Unit.Circuit.Vertex.unitCircuitVertex quarter degree degreeAtLeastTwo 0).value =
      Geometry.Gaussian.UnitCircle.Quarter.unitCircuitMultiplier quarter := by
  simp only [-eq_self, -iff_self, Power.Unit.Circuit.Vertex.unitCircuitVertex,
    Power.Unit.Circuit.Point.unitCircuitPoint,
    Power.Unit.Circuit.Subdivision.unitCircuitParameter_zero,
      Geometry.Gaussian.UnitCircle.Stereographic.unitQuarterPoint_zero,
    Gaussian.Basic.mul_one]
  rfl
end Purelib.RootIsolation.Power.Unit.Circuit.Chain

end

section
public section

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

namespace Purelib.RootIsolation.Power.Unit.Circuit.Chain

open Purelib.Data.Gaussian

/-- Recursively construct the retained suffix of subdivided quarter moves from the supplied bounded start index. -/
@[expose] def unitQuarterChainFrom (quarter : Geometry.Gaussian.UnitCircle.Quarter.UnitCircuitQuarter)
    (degree : Data.Nat.Positive.RootDegree) (degreeAtLeastTwo : 2 ≤ degree.value)
    (start : Nat) : (count : Nat) →
    Power.Unit.Chain.Basic.UnitChain degree degreeAtLeastTwo
      (Power.Unit.Circuit.Vertex.unitCircuitVertex quarter degree degreeAtLeastTwo start)
      (Power.Unit.Circuit.Vertex.unitCircuitVertex quarter degree degreeAtLeastTwo (start + count))
  | 0 => by
      simpa only [-eq_self, -iff_self, Nat.add_zero] using
        (Power.Unit.Chain.Basic.UnitChain.nil
          (Power.Unit.Circuit.Vertex.unitCircuitVertex quarter degree degreeAtLeastTwo start))
  | count + 1 => by
      let step : Power.Unit.Move.Budget.UnitMoveSmall
          (Power.Unit.Circuit.Vertex.unitCircuitVertex quarter degree degreeAtLeastTwo start).unit
          (Power.Unit.Circuit.Vertex.unitCircuitVertex quarter degree degreeAtLeastTwo (start + 1)).unit
          degree degreeAtLeastTwo :=
        ⟨Power.Unit.Circuit.Point.unitCircuitSubdivision_small quarter degree degreeAtLeastTwo start,
          (Power.Unit.Circuit.Point.unitCircuitSubdivision_liftMargin quarter degree degreeAtLeastTwo
            start).le⟩
      let tail : Power.Unit.Chain.Basic.UnitChain degree degreeAtLeastTwo
          (Power.Unit.Circuit.Vertex.unitCircuitVertex quarter degree degreeAtLeastTwo (start + 1))
          (Power.Unit.Circuit.Vertex.unitCircuitVertex quarter degree degreeAtLeastTwo
            (start + 1 + count)) :=
        Purelib.RootIsolation.Power.Unit.Circuit.Chain.unitQuarterChainFrom quarter degree degreeAtLeastTwo (start + 1)
          count
      let raw : Power.Unit.Chain.Basic.UnitChain degree degreeAtLeastTwo
          (Power.Unit.Circuit.Vertex.unitCircuitVertex quarter degree degreeAtLeastTwo start)
          (Power.Unit.Circuit.Vertex.unitCircuitVertex quarter degree degreeAtLeastTwo
            (start + 1 + count)) :=
        Power.Unit.Chain.Basic.UnitChain.cons step tail
      have endpoint : start + 1 + count = start + (count + 1) := by omega
      exact Power.Unit.Chain.Basic.UnitChain.castFinish
        (congrArg
          (Power.Unit.Circuit.Vertex.unitCircuitVertex quarter degree degreeAtLeastTwo) endpoint) raw
end Purelib.RootIsolation.Power.Unit.Circuit.Chain

end

section
public section

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

namespace Purelib.RootIsolation.Power.Unit.Circuit.Chain

open Purelib.Data.Gaussian

/-- Construct the complete quarter chain from the retained finite subdivision and its original move bounds. -/
@[expose] def unitQuarterChain (quarter : Geometry.Gaussian.UnitCircle.Quarter.UnitCircuitQuarter) (degree :
  Data.Nat.Positive.RootDegree)
    (degreeAtLeastTwo : 2 ≤ degree.value) :
    Power.Unit.Chain.Basic.UnitChain degree degreeAtLeastTwo
      (Power.Unit.Circuit.Vertex.unitCircuitVertex quarter degree degreeAtLeastTwo 0)
      (Power.Unit.Circuit.Vertex.unitCircuitVertex quarter degree degreeAtLeastTwo
        (Power.Unit.Circuit.Subdivision.unitCircuitStepCount degree degreeAtLeastTwo)) :=
  Power.Unit.Chain.Basic.UnitChain.castFinish
    (congrArg (Power.Unit.Circuit.Vertex.unitCircuitVertex quarter degree degreeAtLeastTwo)
      (Nat.zero_add (Power.Unit.Circuit.Subdivision.unitCircuitStepCount degree degreeAtLeastTwo)))
    (Power.Unit.Circuit.Chain.unitQuarterChainFrom quarter degree degreeAtLeastTwo 0
      (Power.Unit.Circuit.Subdivision.unitCircuitStepCount degree degreeAtLeastTwo))
end Purelib.RootIsolation.Power.Unit.Circuit.Chain

end

section
public section

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

namespace Purelib.RootIsolation.Power.Unit.Circuit.Chain

open Purelib.Data.Gaussian

/-- Four explicitly subdivided rational quarter-arcs, joined into one closed
positive unit-parameter circuit. -/
@[expose] def unitCircuitChain (degree : Data.Nat.Positive.RootDegree)
    (degreeAtLeastTwo : 2 ≤ degree.value) :
    Power.Unit.Chain.Basic.UnitChain degree degreeAtLeastTwo
      (Power.Unit.Circuit.Vertex.unitCircuitVertex .first degree degreeAtLeastTwo 0)
      (Power.Unit.Circuit.Vertex.unitCircuitVertex .first degree degreeAtLeastTwo 0) :=
  (((((((Power.Unit.Circuit.Chain.unitQuarterChain .first degree degreeAtLeastTwo).append
      (Power.Unit.Circuit.Chain.unitCircuitFirstSecondJoin degree degreeAtLeastTwo)).append
      (Power.Unit.Circuit.Chain.unitQuarterChain .second degree degreeAtLeastTwo)).append
      (Power.Unit.Circuit.Chain.unitCircuitSecondThirdJoin degree degreeAtLeastTwo)).append
      (Power.Unit.Circuit.Chain.unitQuarterChain .third degree degreeAtLeastTwo)).append
      (Power.Unit.Circuit.Chain.unitCircuitThirdFourthJoin degree degreeAtLeastTwo)).append
      (Power.Unit.Circuit.Chain.unitQuarterChain .fourth degree degreeAtLeastTwo)).append
      (Power.Unit.Circuit.Chain.unitCircuitFourthFirstJoin degree degreeAtLeastTwo)
end Purelib.RootIsolation.Power.Unit.Circuit.Chain

end

section
public section

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

namespace Purelib.RootIsolation.Power.Unit.Circuit.Chain

open Purelib.Data.Gaussian

/-- Every edge of the retained quarter suffix satisfies its original half-plane and product formulas. -/
private theorem unitQuarterChainFrom_rotationFormulas
    (quarter : Geometry.Gaussian.UnitCircle.Quarter.UnitCircuitQuarter) (degree : Data.Nat.Positive.RootDegree)
    (degreeAtLeastTwo : 2 ≤ degree.value) (start : Nat) :
    ∀ (count : Nat),
      start + count ≤ Power.Unit.Circuit.Subdivision.unitCircuitStepCount degree degreeAtLeastTwo →
      Power.Unit.Chain.Basic.UnitChain.RotationFormulas quarter
        (Power.Unit.Circuit.Chain.unitQuarterChainFrom quarter degree degreeAtLeastTwo start count)
  | 0, _ => by
      have chainEq :
          Power.Unit.Circuit.Chain.unitQuarterChainFrom quarter degree degreeAtLeastTwo start 0 =
            Power.Unit.Chain.Basic.UnitChain.nil
              (Power.Unit.Circuit.Vertex.unitCircuitVertex quarter degree degreeAtLeastTwo start) := by
        rfl
      rw [chainEq]
      exact Power.Unit.Chain.Rotation.UnitChain.RotationFormulas.nil
        (degree := degree) (degreeAtLeastTwo := degreeAtLeastTwo) quarter
        (Power.Unit.Circuit.Vertex.unitCircuitVertex quarter degree degreeAtLeastTwo start)
  | count + 1, bound => by
      have edgeBound : start <
          Power.Unit.Circuit.Subdivision.unitCircuitStepCount degree degreeAtLeastTwo := by omega
      have tailBound : start + 1 + count ≤
          Power.Unit.Circuit.Subdivision.unitCircuitStepCount degree degreeAtLeastTwo := by omega
      let step : Power.Unit.Move.Budget.UnitMoveSmall
          (Power.Unit.Circuit.Vertex.unitCircuitVertex quarter degree degreeAtLeastTwo start).unit
          (Power.Unit.Circuit.Vertex.unitCircuitVertex quarter degree degreeAtLeastTwo (start + 1)).unit
          degree degreeAtLeastTwo :=
        ⟨Power.Unit.Circuit.Point.unitCircuitSubdivision_small quarter degree degreeAtLeastTwo start,
          (Power.Unit.Circuit.Point.unitCircuitSubdivision_liftMargin quarter degree degreeAtLeastTwo
            start).le⟩
      let tail : Power.Unit.Chain.Basic.UnitChain degree degreeAtLeastTwo
          (Power.Unit.Circuit.Vertex.unitCircuitVertex quarter degree degreeAtLeastTwo (start + 1))
          (Power.Unit.Circuit.Vertex.unitCircuitVertex quarter degree degreeAtLeastTwo
            (start + 1 + count)) :=
        Power.Unit.Circuit.Chain.unitQuarterChainFrom quarter degree degreeAtLeastTwo (start + 1) count
      have tailFormulas : Power.Unit.Chain.Basic.UnitChain.RotationFormulas quarter tail := by
        exact Purelib.RootIsolation.Power.Unit.Circuit.Chain.unitQuarterChainFrom_rotationFormulas quarter degree
          degreeAtLeastTwo (start + 1) count tailBound
      have edgeHalfPlane := Power.Unit.Circuit.Clearance.unitCircuitRotatedEdgeHalfPlaneFormula quarter
        degree degreeAtLeastTwo edgeBound
      have edgeProduct := Power.Unit.Circuit.Product.unitCircuitEdgeProductFormula quarter degree
        degreeAtLeastTwo edgeBound
      let raw : Power.Unit.Chain.Basic.UnitChain degree degreeAtLeastTwo
          (Power.Unit.Circuit.Vertex.unitCircuitVertex quarter degree degreeAtLeastTwo start)
          (Power.Unit.Circuit.Vertex.unitCircuitVertex quarter degree degreeAtLeastTwo
            (start + 1 + count)) :=
        Power.Unit.Chain.Basic.UnitChain.cons step tail
      have rawFormulas : Power.Unit.Chain.Basic.UnitChain.RotationFormulas quarter raw := by
        exact Power.Unit.Chain.Rotation.UnitChain.RotationFormulas.cons quarter edgeHalfPlane edgeProduct
          tailFormulas
      have endpoint : start + 1 + count = start + (count + 1) := by omega
      have castFormulas := Power.Unit.Chain.Rotation.UnitChain.RotationFormulas.castFinish quarter
        (congrArg (Power.Unit.Circuit.Vertex.unitCircuitVertex quarter degree degreeAtLeastTwo) endpoint)
        rawFormulas
      simpa only [-eq_self, -iff_self, Power.Unit.Circuit.Chain.unitQuarterChainFrom, step, tail, raw] using
        castFormulas
end Purelib.RootIsolation.Power.Unit.Circuit.Chain

end

section
public section

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

namespace Purelib.RootIsolation.Power.Unit.Circuit.Chain

open Purelib.Data.Gaussian

/-- The complete retained quarter chain satisfies its original half-plane and product formulas. -/
theorem unitQuarterChain_rotationFormulas
    (quarter : Geometry.Gaussian.UnitCircle.Quarter.UnitCircuitQuarter) (degree : Data.Nat.Positive.RootDegree)
    (degreeAtLeastTwo : 2 ≤ degree.value) :
    Power.Unit.Chain.Basic.UnitChain.RotationFormulas quarter
      (Power.Unit.Circuit.Chain.unitQuarterChain quarter degree degreeAtLeastTwo) := by
  exact Power.Unit.Chain.Rotation.UnitChain.RotationFormulas.castFinish quarter
    (congrArg (Power.Unit.Circuit.Vertex.unitCircuitVertex quarter degree degreeAtLeastTwo)
      (Nat.zero_add (Power.Unit.Circuit.Subdivision.unitCircuitStepCount degree degreeAtLeastTwo)))
    (Power.Unit.Circuit.Chain.unitQuarterChainFrom_rotationFormulas quarter degree degreeAtLeastTwo 0
      (Power.Unit.Circuit.Subdivision.unitCircuitStepCount degree degreeAtLeastTwo) (by omega))
end Purelib.RootIsolation.Power.Unit.Circuit.Chain

end
