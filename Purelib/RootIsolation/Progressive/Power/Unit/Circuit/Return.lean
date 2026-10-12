module
import Purelib.Data.Int.Division
import Purelib.Tactic.QuotientFreeOmega
import Purelib.Data.Nat.Subtraction
public import Purelib.Algebra.NatCast

import Purelib.Data.Fin.Bijection.Iteration
import Purelib.Data.Gaussian.Basic
public import Purelib.Data.Nat.Divisibility.Witness
import Purelib.Data.Nat.Positive
import Purelib.Polynomial.Dense.Basic
import Purelib.Polynomial.Dense.Gaussian.Monomial.Coordinate
import Purelib.Polynomial.Dense.Gaussian.Power.Coordinate
import Purelib.Polynomial.Winding.Polygon.Basic
import Purelib.Polynomial.Winding.Polygon.Comparison
import Purelib.Polynomial.Winding.Polygon.Power
import Purelib.RootIsolation.Power.Unit.Circuit.Chain
import Purelib.RootIsolation.Power.Unit.Circuit.Vertex
public import Purelib.RootIsolation.Power.Unit.Circuit.Winding
public import Purelib.RootIsolation.Progressive.Power.Unit.Chain.Iteration
public import Purelib.RootIsolation.Progressive.Power.Unit.Circuit.Loop
import Purelib.Geometry.Gaussian.UnitCircle.Basic
import Purelib.Geometry.Gaussian.UnitCircle.Quarter
import Purelib.Polynomial.Winding.Polygon.Normalized
import Purelib.RootIsolation.Power.Unit.Chain.Basic
import Purelib.RootIsolation.Power.Unit.Chain.Iteration
import Purelib.RootIsolation.Progressive.Chamber.Frame
import Purelib.RootIsolation.Progressive.Chamber.Path.Basic
import Purelib.RootIsolation.Progressive.Chamber.Path.Transport
import Purelib.RootIsolation.Progressive.Power.Unit.Chain.Lift
import Purelib.RootIsolation.Progressive.Power.Unit.Chain.Path
import Purelib.RootIsolation.Progressive.Power.Unit.Vertex
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

namespace Purelib.RootIsolation.Progressive.Power.Unit.Circuit.Return

open Purelib.Data.Gaussian

/-- Any computed return of the explicit unit-circuit lift yields the exact
natural divisibility identity `d * k = circuits`.  The integer `k` is first
constructed by the finite phase scanner; positivity of `d` and the
nonnegative circuit count then shows that it is a natural number. -/
@[expose] def unitCircuitReturnWindingCertificate
    (degree : Data.Nat.Positive.RootDegree) (degreeAtLeastTwo : 2 ≤ degree.value)
    (index : ((Power.Unit.Circuit.Vertex.unitCircuitVertex .first degree degreeAtLeastTwo 0).frame
      degree degreeAtLeastTwo).Index)
    (circuits : Nat)
    (returned : Data.Fin.Bijection.iterateForward
      (Progressive.Power.Unit.Circuit.Loop.unitCircuitLoop degree degreeAtLeastTwo).monodromy circuits index =
        index) :
    Data.Nat.Divisibility.Witness.ReturnWindingCertificate degree circuits := by
  let vertex := Power.Unit.Circuit.Vertex.unitCircuitVertex .first degree degreeAtLeastTwo 0
  let circuit := Power.Unit.Circuit.Chain.unitCircuitChain degree degreeAtLeastTwo
  let repeated := circuit.repeatClosed circuits
  have repeatedReturned : repeated.toPath.finalIndex index = index := by
    rw [Power.Unit.Chain.Basic.UnitChain.repeatClosed_finalIndex]
    simpa only [-eq_self, -iff_self, Progressive.Power.Unit.Circuit.Loop.unitCircuitLoop, circuit, repeated, vertex]
      using returned
  let normalized := repeated.normalizedLiftOfReturn index repeatedReturned
  have powerWinding := Winding.Polygon.Power.closedRaw_coordinatePositivePower
    (vertex.ownerAnchor degree degreeAtLeastTwo index)
    (repeated.liftVertices index) (degree.value - 1)
    (repeated.closedPositivePowerFormula_of_return index repeatedReturned
      (degree.value - 1))
  have exponent : degree.value - 1 + 1 = degree.value :=
    Nat.Subtraction.sub_add_cancel degree.positive
  have castExponent : ((degree.value - 1 + 1 : Nat) : Int) =
      (degree.value : Int) := by
    rw [exponent]
  rw [castExponent] at powerWinding
  have compared := Winding.Polygon.Comparison.closedRaw_eq_of_homotopy
    (Dense.Gaussian.Power.Coordinate.coordinatePositivePower (degree.value - 1))
    Dense.Gaussian.Monomial.Coordinate.coordinatePolynomial
    (vertex.ownerAnchor degree degreeAtLeastTwo index)
    (repeated.liftVertices index) vertex.value
    repeated.liftParameterVertices
    (repeated.closedHomotopyFormula_of_return index repeatedReturned)
  have parameterWinding := Power.Unit.Circuit.Winding.repeatedUnitCircuitParameterPolygon_windingFour
    degree degreeAtLeastTwo circuits
  have fourIdentity :
      (4 : Int) * ((degree.value : Int) * normalized.winding) =
        4 * (circuits : Int) := by
    calc
      (4 : Int) * ((degree.value : Int) * normalized.winding) =
          (degree.value : Int) * (4 * normalized.winding) := by ring1
      _ = (degree.value : Int) *
          Winding.Polygon.Basic.closedRaw
            Dense.Gaussian.Monomial.Coordinate.coordinatePolynomial
            (vertex.ownerAnchor degree degreeAtLeastTwo index)
            (repeated.liftVertices index) := by
        rw [normalized.raw_eq]
      _ = Winding.Polygon.Basic.closedRaw
          (Dense.Gaussian.Power.Coordinate.coordinatePositivePower (degree.value - 1))
          (vertex.ownerAnchor degree degreeAtLeastTwo index)
          (repeated.liftVertices index) := powerWinding.symm
      _ = Winding.Polygon.Basic.closedRaw
          Dense.Gaussian.Monomial.Coordinate.coordinatePolynomial vertex.value
          repeated.liftParameterVertices := compared.symm
      _ = 4 * (circuits : Int) := parameterWinding
  have intIdentity :
      (degree.value : Int) * normalized.winding = (circuits : Int) :=
    by
      have divided := congrArg (fun value : Int => value / 4) fourIdentity
      rw [Int.Division.mul_ediv_cancel_left _ (by decide : (4 : Int) ≠ 0),
        Int.Division.mul_ediv_cancel_left _ (by decide : (4 : Int) ≠ 0)] at divided
      exact divided
  cases windingShape : normalized.winding with
  | ofNat liftWinding =>
      refine
        { liftWinding := liftWinding
          power_identity := ?_ }
      apply Int.ofNat_inj.mp
      rw [Algebra.NatCast.mul]
      simpa only [-eq_self, -iff_self, windingShape, Int.ofNat_eq_natCast] using intIdentity
  | negSucc magnitude =>
      rw [windingShape, Int.ofNat_mul_negSucc] at intIdentity
      have productNonzero : degree.value * Nat.succ magnitude ≠ 0 :=
        Nat.ne_of_gt (Nat.mul_pos degree.positive (Nat.zero_lt_succ _))
      cases productShape : degree.value * Nat.succ magnitude with
      | zero => exact (productNonzero productShape).elim
      | succ preceding =>
          rw [productShape] at intIdentity
          exact Int.noConfusion intIdentity
end Purelib.RootIsolation.Progressive.Power.Unit.Circuit.Return

end
