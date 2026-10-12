module
import Purelib.Data.Nat.Subtraction

import Purelib.Data.Gaussian.Basic
public import Purelib.Data.Nat.Positive
import Purelib.Data.Rat.Fraction
public import Purelib.Geometry.Rational.Box.UnitSquare.Circuit
import Purelib.Polynomial.Dense.Basic
import Purelib.Polynomial.Dense.Gaussian.Monomial.Coordinate
public import Purelib.Polynomial.Dense.Gaussian.Power.Coordinate
public import Purelib.Polynomial.Winding.Box.Basic
import Purelib.Polynomial.Winding.Box.Coordinate
import Purelib.Polynomial.Winding.Box.Coordinate.Power
import Purelib.Data.Rat.Fraction.Arithmetic
import Purelib.Data.Rat.Fraction.Order.Basic
import Purelib.Geometry.Rational.Box.Basic
import Purelib.Geometry.Rational.Box.Subdivision

open Purelib

open Purelib.Data.Rat

open Purelib.Geometry.Rational

open Purelib.Polynomial

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

namespace Purelib.RootIsolation.Winding.Box.UnitSquare

open Purelib.Data.Gaussian

open Purelib.Data.Nat

/-- Raising the circuit coordinate to the `d`th power multiplies its finite
raw winding by exactly `d`.  This is the arithmetic equality later applied
to a closed owner lift. -/
theorem parameterCircuit_power_windingFour (degree :
  Data.Nat.Positive.RootDegree) :
    Winding.Box.Basic.quadrupledBoxWinding
        (Dense.Gaussian.Power.Coordinate.coordinatePositivePower (degree.value - 1))
        Box.UnitSquare.Circuit.parameterBox =
      (4 : Int) * degree.value := by
  have power :=
    Winding.Box.Coordinate.Power.quadrupledBoxWinding_coordinatePositivePower
      (R := (1 : Fraction.Rational)) (by decide) (degree.value - 1)
  have exponent : degree.value - 1 + 1 = degree.value :=
    Subtraction.sub_add_cancel degree.positive
  have castExponent : ((degree.value - 1 : Nat) : Int) + 1 =
      (degree.value : Int) := by
    rw [← Int.natCast_one, ← Int.natCast_add, exponent]
  rw [castExponent] at power
  simpa only [Box.UnitSquare.Circuit.parameterBox] using power
end Purelib.RootIsolation.Winding.Box.UnitSquare

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

namespace Purelib.RootIsolation.Winding.Box.UnitSquare

open Purelib.Data.Gaussian

/-- The coordinate polynomial has normalized winding one on the displayed parameter square. -/
theorem parameterCircuit_winding :
    Winding.Box.Basic.boxWinding
      Dense.Gaussian.Monomial.Coordinate.coordinatePolynomial Box.UnitSquare.Circuit.parameterBox = 1 := by
  exact (Winding.Box.Coordinate.coordinate_symmetric_normalization
    (R := (1 : Fraction.Rational)) (by decide)).2.2
end Purelib.RootIsolation.Winding.Box.UnitSquare

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

namespace Purelib.RootIsolation.Winding.Box.UnitSquare

open Purelib.Data.Gaussian

/-- The displayed parameter square makes exactly one positive circuit of
zero in the repository's integer-valued raw convention. -/
theorem parameterCircuit_windingFour :
    Winding.Box.Basic.quadrupledBoxWinding
      Dense.Gaussian.Monomial.Coordinate.coordinatePolynomial Box.UnitSquare.Circuit.parameterBox = 4 := by
  exact (Winding.Box.Coordinate.coordinate_symmetric_normalization
    (R := (1 : Fraction.Rational)) (by decide)).1
end Purelib.RootIsolation.Winding.Box.UnitSquare

end
