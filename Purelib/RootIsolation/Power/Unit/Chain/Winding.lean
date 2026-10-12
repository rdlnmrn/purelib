module
import Purelib.Data.Int.Arithmetic
import Purelib.Algebra.NatCast

import Purelib.Data.Gaussian.Basic
import Purelib.Data.Nat.Positive
import Purelib.Geometry.Gaussian.UnitCircle.Basic
import Purelib.Polynomial.Dense.Basic
import Purelib.Polynomial.Dense.Gaussian.Basic
import Purelib.Polynomial.Dense.Gaussian.Monomial.Coordinate
public import Purelib.Polynomial.Winding.Polygon.Basic
import Purelib.Polynomial.Winding.Polygon.Coordinate
import Purelib.RootIsolation.Power.Unit.Chain.Basic
public import Purelib.RootIsolation.Power.Unit.Chain.Iteration
public import Purelib.RootIsolation.Power.Unit.Chain.Vertices
import Purelib.Tactic.Ring

open Purelib

open Purelib.Polynomial

open Purelib.RootIsolation

open Purelib.Data

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

namespace Purelib.RootIsolation.Power.Unit.Chain.Basic

open Purelib.Data.Gaussian
namespace UnitChain

/-- Read the original polynomial's raw winding along the retained unit-chain parameter vertices. -/
@[expose] def parameterRaw
    {degree : Data.Nat.Positive.RootDegree} {degreeAtLeastTwo : 2 ≤ degree.value}
    {start finish : Geometry.Gaussian.UnitCircle.Basic.UnitVertex} (p :
      Polynomial.Dense.Gaussian.Basic.CanonicalCoefficients.CoefficientPolynomial)
    (chain : Power.Unit.Chain.Basic.UnitChain degree degreeAtLeastTwo start finish) : Int :=
  Winding.Polygon.Basic.chainRaw p start.value chain.vertices
end UnitChain
end Purelib.RootIsolation.Power.Unit.Chain.Basic

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

namespace Purelib.RootIsolation.Power.Unit.Chain.Basic

open Purelib.Data.Gaussian
namespace UnitChain

/-- Raw parameter winding adds under concatenation of the original unit chains. -/
theorem parameterRaw_append
    {degree : Data.Nat.Positive.RootDegree} {degreeAtLeastTwo : 2 ≤ degree.value}
    {start middle finish : Geometry.Gaussian.UnitCircle.Basic.UnitVertex} (p :
      Polynomial.Dense.Gaussian.Basic.CanonicalCoefficients.CoefficientPolynomial)
    (first : Power.Unit.Chain.Basic.UnitChain degree degreeAtLeastTwo start middle)
    (second : Power.Unit.Chain.Basic.UnitChain degree degreeAtLeastTwo middle finish) :
    Power.Unit.Chain.Basic.UnitChain.parameterRaw p (first.append second) =
      Power.Unit.Chain.Basic.UnitChain.parameterRaw p first + Power.Unit.Chain.Basic.UnitChain.parameterRaw p second :=
        by
  unfold Power.Unit.Chain.Basic.UnitChain.parameterRaw
  rw [Power.Unit.Chain.Basic.UnitChain.vertices_append, Winding.Polygon.Basic.chainRaw_append,
    first.vertices_terminal]
end UnitChain
end Purelib.RootIsolation.Power.Unit.Chain.Basic

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

namespace Purelib.RootIsolation.Power.Unit.Chain.Basic

open Purelib.Data.Gaussian
namespace UnitChain

/-- Transporting the finish vertex along equality preserves raw parameter winding. -/
theorem parameterRaw_castFinish
    {degree : Data.Nat.Positive.RootDegree} {degreeAtLeastTwo : 2 ≤ degree.value}
    {start left right : Geometry.Gaussian.UnitCircle.Basic.UnitVertex} (p :
      Polynomial.Dense.Gaussian.Basic.CanonicalCoefficients.CoefficientPolynomial)
    (same : left = right)
    (chain : Power.Unit.Chain.Basic.UnitChain degree degreeAtLeastTwo start left) :
    Power.Unit.Chain.Basic.UnitChain.parameterRaw p (Power.Unit.Chain.Basic.UnitChain.castFinish same chain) =
      Power.Unit.Chain.Basic.UnitChain.parameterRaw p chain := by
  subst right
  rfl
end UnitChain
end Purelib.RootIsolation.Power.Unit.Chain.Basic

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

namespace Purelib.RootIsolation.Power.Unit.Chain.Basic

open Purelib.Data.Gaussian
namespace UnitChain

/-- The coordinate winding of a connector between equal displayed parameter values is zero. -/
theorem parameterRaw_equalValue
    {degree : Data.Nat.Positive.RootDegree} {degreeAtLeastTwo : 2 ≤ degree.value}
    {left right : Geometry.Gaussian.UnitCircle.Basic.UnitVertex} (same : left.value = right.value) :
    Power.Unit.Chain.Basic.UnitChain.parameterRaw Dense.Gaussian.Monomial.Coordinate.coordinatePolynomial
      (Power.Unit.Chain.Basic.UnitChain.equalValue
        (degree := degree) (degreeAtLeastTwo := degreeAtLeastTwo) same) = 0 := by
  unfold Power.Unit.Chain.Basic.UnitChain.parameterRaw Power.Unit.Chain.Basic.UnitChain.equalValue
  simp only [-eq_self, -iff_self, Power.Unit.Chain.Basic.UnitChain.vertices, Winding.Polygon.Basic.chainRaw]
  rw [same]
  rw [Winding.Polygon.Coordinate.coordinate_segment_self_doubledWinding]
  exact Int.Arithmetic.zero_add 0
end UnitChain
end Purelib.RootIsolation.Power.Unit.Chain.Basic

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

namespace Purelib.RootIsolation.Power.Unit.Chain.Basic

open Purelib.Data.Gaussian
namespace UnitChain

/-- The empty unit chain has zero raw parameter winding. -/
@[simp] theorem parameterRaw_nil
    {degree : Data.Nat.Positive.RootDegree} {degreeAtLeastTwo : 2 ≤ degree.value}
    (p : Polynomial.Dense.Gaussian.Basic.CanonicalCoefficients.CoefficientPolynomial) (vertex :
      Geometry.Gaussian.UnitCircle.Basic.UnitVertex) :
    Power.Unit.Chain.Basic.UnitChain.parameterRaw (degree := degree) (degreeAtLeastTwo := degreeAtLeastTwo)
      p (Power.Unit.Chain.Basic.UnitChain.nil vertex) = 0 := rfl
end UnitChain
end Purelib.RootIsolation.Power.Unit.Chain.Basic

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

namespace Purelib.RootIsolation.Power.Unit.Chain.Basic

open Purelib.Data.Gaussian
namespace UnitChain

/-- Repeating a closed chain multiplies its original raw parameter winding by the finite repetition count. -/
theorem parameterRaw_repeatClosed
    {degree : Data.Nat.Positive.RootDegree} {degreeAtLeastTwo : 2 ≤ degree.value}
    {vertex : Geometry.Gaussian.UnitCircle.Basic.UnitVertex} (p :
      Polynomial.Dense.Gaussian.Basic.CanonicalCoefficients.CoefficientPolynomial)
    (chain : Power.Unit.Chain.Basic.UnitChain degree degreeAtLeastTwo vertex vertex) :
    ∀ circuits : Nat,
      Power.Unit.Chain.Basic.UnitChain.parameterRaw p (chain.repeatClosed circuits) =
        (circuits : Int) * Power.Unit.Chain.Basic.UnitChain.parameterRaw p chain
  | 0 => by
      simp only [-eq_self, -iff_self, Power.Unit.Chain.Basic.UnitChain.repeatClosed,
        Power.Unit.Chain.Basic.UnitChain.parameterRaw_nil]
      ring1
  | circuits + 1 => by
      rw [Power.Unit.Chain.Basic.UnitChain.repeatClosed, Power.Unit.Chain.Basic.UnitChain.parameterRaw_append,
        Purelib.RootIsolation.Power.Unit.Chain.Basic.UnitChain.parameterRaw_repeatClosed p chain circuits]
      simp only [-eq_self, -iff_self, Algebra.NatCast.add, Nat.cast_one]
      ring1
end UnitChain
end Purelib.RootIsolation.Power.Unit.Chain.Basic

end
