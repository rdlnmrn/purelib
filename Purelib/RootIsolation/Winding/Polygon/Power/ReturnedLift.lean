module
public import Purelib.Data.Nat.Subtraction
meta import Purelib.Elab.ConstructiveInjectivity
import Purelib.Data.Int.Arithmetic

import Purelib.Data.Gaussian.Basic
public import Purelib.Data.Nat.Divisibility.Witness
import Purelib.Data.Nat.Positive
import Purelib.Geometry.Rational.Polygon.Chain
import Purelib.Polynomial.Dense.Basic
import Purelib.Polynomial.Dense.Gaussian.Monomial.Coordinate
import Purelib.Polynomial.Dense.Gaussian.Power.Coordinate
import Purelib.Polynomial.Winding.Polygon.Basic
public import Purelib.Polynomial.Winding.Polygon.Comparison
public import Purelib.Polynomial.Winding.Polygon.Power
public import Purelib.RootIsolation.Winding.Polygon.UnitSquare
public import Mathlib.Data.Nat.Cast.Basic
import Purelib.Tactic.Ring

open Purelib.Data

open Purelib

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

namespace Purelib.RootIsolation.Winding.Polygon.Power

open Purelib.Data.Gaussian

/-! ### Returned rational power lifts -/

set_option genInjectivity false in
/-- Fully finite evidence attached to one returned owner after
`additional+1` positive parameter circuits.  The source is a rational
polygonal sample lift.  Its power is compared, edge by edge, with the
explicitly repeated parameter square. -/
structure ReturnedLift (degree :
  Data.Nat.Positive.RootDegree) (additional : Nat) where
  /-- The retained starting Gaussian coordinate of the finite lifted polygon. -/ liftBase : Gaussian.Basic.Canonical
  /-- The retained ordered vertices of the finite lifted polygon. -/ liftVertices : List Gaussian.Basic.Canonical
  /-- The natural winding count retained for the lifted polygon. -/ liftWinding : Nat
  /-- The lifted polygon's raw coordinate winding is exactly four times its retained natural winding. -/ liftNormalized
    :
    Winding.Polygon.Basic.closedRaw
        Dense.Gaussian.Monomial.Coordinate.coordinatePolynomial
        liftBase liftVertices =
      (4 : Int) * liftWinding
  /-- The original finite positive-power winding formula for the retained lift. -/ powerFormula :
    Winding.Polygon.Power.ClosedPositivePowerFormula
      liftBase liftVertices (degree.value - 1)
  /-- The retained edgewise homotopy comparing the powered lift to the repeated original parameter square. -/ comparison
    : Winding.Polygon.Comparison.ClosedHomotopyFormula
    (Dense.Gaussian.Power.Coordinate.coordinatePositivePower (degree.value - 1))
    Dense.Gaussian.Monomial.Coordinate.coordinatePolynomial
    liftBase liftVertices Winding.Polygon.UnitSquare.parameterBase
    (Polygon.Chain.repeatClosedVertices
      Winding.Polygon.UnitSquare.parameterBase Winding.Polygon.UnitSquare.parameterVertices additional)

constructive_injectivity ReturnedLift

end Purelib.RootIsolation.Winding.Polygon.Power

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

namespace Purelib.RootIsolation.Winding.Polygon.Power.ReturnedLift

open Purelib.Data.Gaussian

/-- The finite product and Rouché telescopes turn a returned rational lift
into the exact natural identity `d * Wind(lift) = circuits`. -/
def returnWindingCertificate
    {degree : Data.Nat.Positive.RootDegree} {additional : Nat}
    (lift : ReturnedLift degree additional) :
    Data.Nat.Divisibility.Witness.ReturnWindingCertificate degree (additional + 1) := by
  have exponent : degree.value - 1 + 1 = degree.value :=
    Data.Nat.Subtraction.sub_add_cancel degree.positive
  have castExponent : ((degree.value - 1 + 1 : Nat) : Int) =
      (degree.value : Int) := by
    rw [exponent]
  have powerWinding :=
    Winding.Polygon.Power.closedRaw_coordinatePositivePower
      lift.liftBase lift.liftVertices (degree.value - 1) lift.powerFormula
  rw [castExponent] at powerWinding
  have compared := Winding.Polygon.Comparison.closedRaw_eq_of_homotopy
    (Dense.Gaussian.Power.Coordinate.coordinatePositivePower (degree.value - 1))
    Dense.Gaussian.Monomial.Coordinate.coordinatePolynomial
    lift.liftBase lift.liftVertices Winding.Polygon.UnitSquare.parameterBase
    (Polygon.Chain.repeatClosedVertices
      Winding.Polygon.UnitSquare.parameterBase Winding.Polygon.UnitSquare.parameterVertices additional) lift.comparison
  have parameterWinding := Winding.Polygon.UnitSquare.repeatedParameterPolygon_windingFour additional
  have fourIdentity :
      (4 : Int) *
          ((degree.value : Int) * (lift.liftWinding : Int)) =
        4 * ((additional + 1 : Nat) : Int) := by
    calc
      (4 : Int) *
          ((degree.value : Int) * (lift.liftWinding : Int)) =
        (degree.value : Int) *
          (4 * (lift.liftWinding : Int)) := by ring1
      _ = (degree.value : Int) *
          Winding.Polygon.Basic.closedRaw
            Dense.Gaussian.Monomial.Coordinate.coordinatePolynomial
            lift.liftBase lift.liftVertices := by
        rw [lift.liftNormalized]
      _ = Winding.Polygon.Basic.closedRaw
          (Dense.Gaussian.Power.Coordinate.coordinatePositivePower
            (degree.value - 1)) lift.liftBase lift.liftVertices :=
        powerWinding.symm
      _ = Winding.Polygon.Basic.closedRaw
          Dense.Gaussian.Monomial.Coordinate.coordinatePolynomial Winding.Polygon.UnitSquare.parameterBase
          (Polygon.Chain.repeatClosedVertices
            Winding.Polygon.UnitSquare.parameterBase Winding.Polygon.UnitSquare.parameterVertices additional) :=
              compared.symm
      _ = 4 * ((additional + 1 : Nat) : Int) := parameterWinding
  have intIdentity :
      (degree.value : Int) * (lift.liftWinding : Int) =
        ((additional + 1 : Nat) : Int) := by
    exact Data.Int.Arithmetic.eq_of_mul_eq_mul_left (by decide : (4 : Int) ≠ 0) fourIdentity
  refine
    { liftWinding := lift.liftWinding
      power_identity := ?_ }
  apply Int.ofNat.inj
  change ((degree.value * lift.liftWinding : Nat) : Int) = ((additional + 1 : Nat) : Int)
  rw [Int.natCast_mul]
  exact intIdentity
end Purelib.RootIsolation.Winding.Polygon.Power.ReturnedLift

end
