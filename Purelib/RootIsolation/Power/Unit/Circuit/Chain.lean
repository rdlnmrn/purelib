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

open Purelib.Geometry.Gaussian.UnitCircle

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
    Chain.Basic.UnitChain degree degreeAtLeastTwo
      (Vertex.unitCircuitVertex .first degree degreeAtLeastTwo
        (Subdivision.unitCircuitStepCount degree degreeAtLeastTwo))
      (Vertex.unitCircuitVertex .second degree degreeAtLeastTwo 0) :=
  Chain.Basic.UnitChain.equalValue (Join.unitCircuitQuarters_join degree
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
    Chain.Basic.UnitChain degree degreeAtLeastTwo
      (Vertex.unitCircuitVertex .fourth degree degreeAtLeastTwo
        (Subdivision.unitCircuitStepCount degree degreeAtLeastTwo))
      (Vertex.unitCircuitVertex .first degree degreeAtLeastTwo 0) :=
  Chain.Basic.UnitChain.equalValue (Join.unitCircuitQuarters_join degree
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
    Chain.Basic.UnitChain degree degreeAtLeastTwo
      (Vertex.unitCircuitVertex .second degree degreeAtLeastTwo
        (Subdivision.unitCircuitStepCount degree degreeAtLeastTwo))
      (Vertex.unitCircuitVertex .third degree degreeAtLeastTwo 0) :=
  Chain.Basic.UnitChain.equalValue (Join.unitCircuitQuarters_join degree
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
    Chain.Basic.UnitChain degree degreeAtLeastTwo
      (Vertex.unitCircuitVertex .third degree degreeAtLeastTwo
        (Subdivision.unitCircuitStepCount degree degreeAtLeastTwo))
      (Vertex.unitCircuitVertex .fourth degree degreeAtLeastTwo 0) :=
  Chain.Basic.UnitChain.equalValue (Join.unitCircuitQuarters_join degree
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
    (quarter : Quarter.UnitCircuitQuarter) (degree : Data.Nat.Positive.RootDegree)
    (degreeAtLeastTwo : 2 ≤ degree.value) :
    (Vertex.unitCircuitVertex quarter degree degreeAtLeastTwo
      (Subdivision.unitCircuitStepCount degree degreeAtLeastTwo)).value =
      Quarter.unitCircuitMultiplier quarter * ⟨0, 1⟩ := by
  simp only [-eq_self, -iff_self, Vertex.unitCircuitVertex,
    Point.unitCircuitPoint,
    Subdivision.unitCircuitParameter_last,
      Stereographic.unitQuarterPoint_one]
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
    (quarter : Quarter.UnitCircuitQuarter) (degree : Data.Nat.Positive.RootDegree)
    (degreeAtLeastTwo : 2 ≤ degree.value) :
    (Vertex.unitCircuitVertex quarter degree degreeAtLeastTwo 0).value =
      Quarter.unitCircuitMultiplier quarter := by
  simp only [-eq_self, -iff_self, Vertex.unitCircuitVertex,
    Point.unitCircuitPoint,
    Subdivision.unitCircuitParameter_zero,
      Stereographic.unitQuarterPoint_zero,
    Basic.mul_one]
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
@[expose] def unitQuarterChainFrom (quarter : Quarter.UnitCircuitQuarter)
    (degree : Data.Nat.Positive.RootDegree) (degreeAtLeastTwo : 2 ≤ degree.value)
    (start : Nat) : (count : Nat) →
    Chain.Basic.UnitChain degree degreeAtLeastTwo
      (Vertex.unitCircuitVertex quarter degree degreeAtLeastTwo start)
      (Vertex.unitCircuitVertex quarter degree degreeAtLeastTwo (start + count))
  | 0 => by
      simpa only [-eq_self, -iff_self, Nat.add_zero] using
        (Chain.Basic.UnitChain.nil
          (Vertex.unitCircuitVertex quarter degree degreeAtLeastTwo start))
  | count + 1 => by
      let step : Move.Budget.UnitMoveSmall
          (Vertex.unitCircuitVertex quarter degree degreeAtLeastTwo start).unit
          (Vertex.unitCircuitVertex quarter degree degreeAtLeastTwo (start + 1)).unit
          degree degreeAtLeastTwo :=
        ⟨Point.unitCircuitSubdivision_small quarter degree degreeAtLeastTwo start,
          (Point.unitCircuitSubdivision_liftMargin quarter degree degreeAtLeastTwo
            start).le⟩
      let tail : Chain.Basic.UnitChain degree degreeAtLeastTwo
          (Vertex.unitCircuitVertex quarter degree degreeAtLeastTwo (start + 1))
          (Vertex.unitCircuitVertex quarter degree degreeAtLeastTwo
            (start + 1 + count)) :=
        Chain.unitQuarterChainFrom quarter degree degreeAtLeastTwo (start + 1)
          count
      let raw : Chain.Basic.UnitChain degree degreeAtLeastTwo
          (Vertex.unitCircuitVertex quarter degree degreeAtLeastTwo start)
          (Vertex.unitCircuitVertex quarter degree degreeAtLeastTwo
            (start + 1 + count)) :=
        Chain.Basic.UnitChain.cons step tail
      have endpoint : start + 1 + count = start + (count + 1) := by omega
      exact Chain.Basic.UnitChain.castFinish
        (congrArg
          (Vertex.unitCircuitVertex quarter degree degreeAtLeastTwo) endpoint) raw
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
@[expose] def unitQuarterChain (quarter : Quarter.UnitCircuitQuarter) (degree :
  Data.Nat.Positive.RootDegree)
    (degreeAtLeastTwo : 2 ≤ degree.value) :
    Chain.Basic.UnitChain degree degreeAtLeastTwo
      (Vertex.unitCircuitVertex quarter degree degreeAtLeastTwo 0)
      (Vertex.unitCircuitVertex quarter degree degreeAtLeastTwo
        (Subdivision.unitCircuitStepCount degree degreeAtLeastTwo)) :=
  Chain.Basic.UnitChain.castFinish
    (congrArg (Vertex.unitCircuitVertex quarter degree degreeAtLeastTwo)
      (Nat.zero_add (Subdivision.unitCircuitStepCount degree degreeAtLeastTwo)))
    (unitQuarterChainFrom quarter degree degreeAtLeastTwo 0
      (Subdivision.unitCircuitStepCount degree degreeAtLeastTwo))
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
    Chain.Basic.UnitChain degree degreeAtLeastTwo
      (Vertex.unitCircuitVertex .first degree degreeAtLeastTwo 0)
      (Vertex.unitCircuitVertex .first degree degreeAtLeastTwo 0) :=
  (((((((unitQuarterChain .first degree degreeAtLeastTwo).append
      (unitCircuitFirstSecondJoin degree degreeAtLeastTwo)).append
      (unitQuarterChain .second degree degreeAtLeastTwo)).append
      (unitCircuitSecondThirdJoin degree degreeAtLeastTwo)).append
      (unitQuarterChain .third degree degreeAtLeastTwo)).append
      (unitCircuitThirdFourthJoin degree degreeAtLeastTwo)).append
      (unitQuarterChain .fourth degree degreeAtLeastTwo)).append
      (unitCircuitFourthFirstJoin degree degreeAtLeastTwo)
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
    (quarter : Quarter.UnitCircuitQuarter) (degree : Data.Nat.Positive.RootDegree)
    (degreeAtLeastTwo : 2 ≤ degree.value) (start : Nat) :
    ∀ (count : Nat),
      start + count ≤ Subdivision.unitCircuitStepCount degree degreeAtLeastTwo →
      Chain.Basic.UnitChain.RotationFormulas quarter
        (unitQuarterChainFrom quarter degree degreeAtLeastTwo start count)
  | 0, _ => by
      have chainEq :
          unitQuarterChainFrom quarter degree degreeAtLeastTwo start 0 =
            Chain.Basic.UnitChain.nil
              (Vertex.unitCircuitVertex quarter degree degreeAtLeastTwo start) := by
        rfl
      rw [chainEq]
      exact Chain.Rotation.UnitChain.RotationFormulas.nil
        (degree := degree) (degreeAtLeastTwo := degreeAtLeastTwo) quarter
        (Vertex.unitCircuitVertex quarter degree degreeAtLeastTwo start)
  | count + 1, bound => by
      have edgeBound : start <
          Subdivision.unitCircuitStepCount degree degreeAtLeastTwo := by omega
      have tailBound : start + 1 + count ≤
          Subdivision.unitCircuitStepCount degree degreeAtLeastTwo := by omega
      let step : Move.Budget.UnitMoveSmall
          (Vertex.unitCircuitVertex quarter degree degreeAtLeastTwo start).unit
          (Vertex.unitCircuitVertex quarter degree degreeAtLeastTwo (start + 1)).unit
          degree degreeAtLeastTwo :=
        ⟨Point.unitCircuitSubdivision_small quarter degree degreeAtLeastTwo start,
          (Point.unitCircuitSubdivision_liftMargin quarter degree degreeAtLeastTwo
            start).le⟩
      let tail : Chain.Basic.UnitChain degree degreeAtLeastTwo
          (Vertex.unitCircuitVertex quarter degree degreeAtLeastTwo (start + 1))
          (Vertex.unitCircuitVertex quarter degree degreeAtLeastTwo
            (start + 1 + count)) :=
        unitQuarterChainFrom quarter degree degreeAtLeastTwo (start + 1) count
      have tailFormulas : Chain.Basic.UnitChain.RotationFormulas quarter tail := by
        exact Chain.unitQuarterChainFrom_rotationFormulas quarter degree
          degreeAtLeastTwo (start + 1) count tailBound
      have edgeHalfPlane := Clearance.unitCircuitRotatedEdgeHalfPlaneFormula quarter
        degree degreeAtLeastTwo edgeBound
      have edgeProduct := Product.unitCircuitEdgeProductFormula quarter degree
        degreeAtLeastTwo edgeBound
      let raw : Chain.Basic.UnitChain degree degreeAtLeastTwo
          (Vertex.unitCircuitVertex quarter degree degreeAtLeastTwo start)
          (Vertex.unitCircuitVertex quarter degree degreeAtLeastTwo
            (start + 1 + count)) :=
        Chain.Basic.UnitChain.cons step tail
      have rawFormulas : Chain.Basic.UnitChain.RotationFormulas quarter raw := by
        exact Chain.Rotation.UnitChain.RotationFormulas.cons quarter edgeHalfPlane edgeProduct
          tailFormulas
      have endpoint : start + 1 + count = start + (count + 1) := by omega
      have castFormulas := Chain.Rotation.UnitChain.RotationFormulas.castFinish quarter
        (congrArg (Vertex.unitCircuitVertex quarter degree degreeAtLeastTwo) endpoint)
        rawFormulas
      simpa only [-eq_self, -iff_self, unitQuarterChainFrom, step, tail, raw] using
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
    (quarter : Quarter.UnitCircuitQuarter) (degree : Data.Nat.Positive.RootDegree)
    (degreeAtLeastTwo : 2 ≤ degree.value) :
    Chain.Basic.UnitChain.RotationFormulas quarter
      (unitQuarterChain quarter degree degreeAtLeastTwo) := by
  exact Chain.Rotation.UnitChain.RotationFormulas.castFinish quarter
    (congrArg (Vertex.unitCircuitVertex quarter degree degreeAtLeastTwo)
      (Nat.zero_add (Subdivision.unitCircuitStepCount degree degreeAtLeastTwo)))
    (unitQuarterChainFrom_rotationFormulas quarter degree degreeAtLeastTwo 0
      (Subdivision.unitCircuitStepCount degree degreeAtLeastTwo) (by omega))
end Purelib.RootIsolation.Power.Unit.Circuit.Chain

end
