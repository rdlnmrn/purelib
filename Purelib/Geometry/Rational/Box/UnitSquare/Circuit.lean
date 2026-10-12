module

import Purelib.Data.Gaussian.Basic
import Purelib.Data.Rat.Fraction
import Purelib.Geometry.Rational.Box.Basic
public import Purelib.Geometry.Rational.Box.Subdivision
import Purelib.Polynomial.Dense.Basic
import Init.Prelude
import Purelib.Data.Rat.Fraction.Arithmetic
import Purelib.Data.Rat.Fraction.Order.Basic
meta import Purelib.Elab.Deriving.Repr

open Purelib

open Purelib.Data.Rat

open Purelib.Geometry

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

namespace Purelib.Geometry.Rational.Box.UnitSquare.Circuit
open Purelib.Algebra.Polynomial.DensePolynomial
open Purelib.Data.Gaussian

/-! ## The explicit rational parameter circuit -/

/-- Four oriented sides of the positively oriented unit square. -/
inductive CircuitSide
  /-- The bottom side traversed from left to right. -/ | bottom
  /-- The right side traversed from bottom to top. -/ | right
  /-- The top side traversed from right to left. -/ | top
  /-- The left side traversed from top to bottom. -/ | left
deriving DecidableEq
derive_exposed_repr CircuitSide
end Purelib.Geometry.Rational.Box.UnitSquare.Circuit

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

namespace Purelib.Geometry.Rational.Box.UnitSquare.Circuit
open Purelib.Algebra.Polynomial.DensePolynomial
open Purelib.Data.Gaussian

/-- A rational parameter on one oriented side, with the common parameter running from `-1` to `1`. -/
def circuitValue :
  CircuitSide → Fraction.Rational → Data.Gaussian.Basic.Canonical
  | .bottom, position => ⟨position, -1⟩
  | .right, position => ⟨1, position⟩
  | .top, position => ⟨-position, 1⟩
  | .left, position => ⟨-1, -position⟩
end Purelib.Geometry.Rational.Box.UnitSquare.Circuit

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

namespace Purelib.Geometry.Rational.Box.UnitSquare.Circuit
open Purelib.Algebra.Polynomial.DensePolynomial
open Purelib.Data.Gaussian

/-- No point of any displayed circuit side is the excluded parameter zero. The certificate is coordinatewise and does
not quantify over a completed curve. -/
theorem circuitValue_ne_zero (side :
  CircuitSide) (position : Fraction.Rational) :
    circuitValue side position ≠ 0 := by
  intro zero
  cases side with
  | bottom =>
      have imaginary := congrArg Data.Gaussian.Basic.im zero
      change (-1 : Fraction.Rational) = 0 at imaginary
      exact (by decide : (-1 : Fraction.Rational) ≠ 0) imaginary
  | right =>
      have real := congrArg Data.Gaussian.Basic.re zero
      change (1 : Fraction.Rational) = 0 at real
      exact (by decide : (1 : Fraction.Rational) ≠ 0) real
  | top =>
      have imaginary := congrArg Data.Gaussian.Basic.im zero
      change (1 : Fraction.Rational) = 0 at imaginary
      exact (by decide : (1 : Fraction.Rational) ≠ 0) imaginary
  | left =>
      have real := congrArg Data.Gaussian.Basic.re zero
      change (-1 : Fraction.Rational) = 0 at real
      exact (by decide : (-1 : Fraction.Rational) ≠ 0) real
end Purelib.Geometry.Rational.Box.UnitSquare.Circuit

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

namespace Purelib.Geometry.Rational.Box.UnitSquare.Circuit
open Purelib.Algebra.Polynomial.DensePolynomial
open Purelib.Data.Gaussian

/-- The four rational affine sides join in cyclic order. -/
theorem circuit_sides_join :
    circuitValue .bottom 1 =
      circuitValue .right (-1) ∧
      circuitValue .right 1 =
        circuitValue .top (-1) ∧
      circuitValue .top 1 =
        circuitValue .left (-1) ∧
      circuitValue .left 1 =
        circuitValue .bottom (-1) := by
  exact ⟨rfl, rfl, rfl, rfl⟩
end Purelib.Geometry.Rational.Box.UnitSquare.Circuit

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

namespace Purelib.Geometry.Rational.Box.UnitSquare.Circuit
open Purelib.Algebra.Polynomial.DensePolynomial
open Purelib.Data.Gaussian

/-- The closed unit square centered at zero, containing the four oriented circuit sides. -/
def parameterBox : Rational.Box :=
  Rational.Box.symmetric 1 (by decide)
end Purelib.Geometry.Rational.Box.UnitSquare.Circuit

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

namespace Purelib.Geometry.Rational.Box.UnitSquare.Circuit
open Purelib.Algebra.Polynomial.DensePolynomial
open Purelib.Data.Gaussian

/-- The unit parameter square has strictly positive width and height. -/
theorem parameterBox_proper :
  Geometry.Rational.Box.UnitSquare.Circuit.parameterBox.Proper := by
  constructor <;> decide
end Purelib.Geometry.Rational.Box.UnitSquare.Circuit

end
