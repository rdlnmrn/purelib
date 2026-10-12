module

import Purelib.Data.Gaussian.Basic
import Purelib.Geometry.Rational.Polygon.Chain
import Purelib.Polynomial.Dense.Basic
public import Purelib.Polynomial.Dense.Gaussian.Monomial.Coordinate
public import Purelib.Polynomial.Winding.Polygon.Basic
import Purelib.Polynomial.Winding.Polygon.Repeat
import Purelib.Data.Rat.Fraction
import Purelib.Data.Rat.Fraction.Arithmetic
import Purelib.Tactic.Ring

open Purelib.Data

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

namespace Purelib.RootIsolation.Winding.Polygon.UnitSquare

open Purelib.Data.Gaussian

/-! ### The same circuit as an explicit finite polygon -/

/-- The lower-left Gaussian vertex `(-1, -1)` of the parameter square. -/
def parameterBase : Gaussian.Basic.Canonical := ⟨-1, -1⟩
end Purelib.RootIsolation.Winding.Polygon.UnitSquare

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

namespace Purelib.RootIsolation.Winding.Polygon.UnitSquare

open Purelib.Data.Gaussian

/-- The remaining three vertices of the positively oriented parameter square, in traversal order. -/
def parameterVertices : List Gaussian.Basic.Canonical :=
  [⟨1, -1⟩, ⟨1, 1⟩, ⟨-1, 1⟩]
end Purelib.RootIsolation.Winding.Polygon.UnitSquare

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

namespace Purelib.RootIsolation.Winding.Polygon.UnitSquare

open Purelib.Data.Gaussian

open Purelib.RootIsolation in
/-- Direct kernel calculation of the four affine coordinate edges.  This is
the polygonal form used by a synchronized returned owner lift. -/
theorem parameterPolygon_windingFour :
    Winding.Polygon.Basic.closedRaw
        Dense.Gaussian.Monomial.Coordinate.coordinatePolynomial
        parameterBase parameterVertices = 4 := by
  decide
end Purelib.RootIsolation.Winding.Polygon.UnitSquare

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

namespace Purelib.RootIsolation.Winding.Polygon.UnitSquare

open Purelib.Data.Gaussian

open Purelib.RootIsolation in
/-- Repeating the displayed square `additional+1` times has exactly the
corresponding raw winding. -/
theorem repeatedParameterPolygon_windingFour (additional : Nat)
  :
    Winding.Polygon.Basic.closedRaw
        Dense.Gaussian.Monomial.Coordinate.coordinatePolynomial parameterBase
        (Polygon.Chain.repeatClosedVertices
          parameterBase parameterVertices additional) =
      (4 : Int) * (additional + 1) := by
  rw [Winding.Polygon.Repeat.closedRaw_repeatClosedVertices,
    parameterPolygon_windingFour]
  simp only [Int.natCast_add, Int.natCast_one]
  ring1
end Purelib.RootIsolation.Winding.Polygon.UnitSquare

end
