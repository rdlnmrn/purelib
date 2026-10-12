module
import Purelib.Data.Int.Arithmetic

import Purelib.Data.Gaussian.Basic
import Purelib.Data.Gaussian.Norm.Nonzero
import Purelib.Data.Nat.Positive
import Purelib.Geometry.Gaussian.UnitCircle.Basic
import Purelib.Geometry.Rational.Box.Sample
import Purelib.Geometry.Rational.Polygon.Chain
import Purelib.Polynomial.Clearance.Pair.Basic
import Purelib.Polynomial.Dense.Basic
import Purelib.Polynomial.Dense.Gaussian.Monomial.Coordinate
import Purelib.Polynomial.Dense.Gaussian.Path.Components
import Purelib.Polynomial.Dense.Gaussian.Power.Coordinate
import Purelib.Polynomial.Winding.Polygon.Basic
import Purelib.Polynomial.Winding.Polygon.Comparison
import Purelib.Polynomial.Winding.Polygon.Coordinate
public import Purelib.Polynomial.Winding.Polygon.Normalized
import Purelib.Polynomial.Winding.Polygon.Phase
public import Purelib.Polynomial.Winding.Polygon.Power
import Purelib.Polynomial.Winding.Polygon.Product
import Purelib.RootIsolation.Power.Unit.Box
import Purelib.RootIsolation.Power.Unit.Chain.Basic
import Purelib.RootIsolation.Power.Unit.Chain.Vertices
public import Purelib.RootIsolation.Power.Unit.Chain.Winding
import Purelib.RootIsolation.Power.Unit.Move.Budget
import Purelib.RootIsolation.Power.Unit.Segment.Clearance
import Purelib.RootIsolation.Power.Unit.Segment.Homotopy
import Purelib.RootIsolation.Power.Unit.Segment.Product
import Purelib.RootIsolation.Progressive.Chamber.Path.Transport
import Purelib.RootIsolation.Progressive.Power.Unit.Frame
public import Purelib.RootIsolation.Progressive.Power.Unit.Lift.Formulas
import Purelib.RootIsolation.Progressive.Power.Unit.Lift.Vertices
import Purelib.RootIsolation.Progressive.Power.Unit.Move.Path
import Purelib.RootIsolation.Progressive.Power.Unit.Vertex
public import Purelib.RootIsolation.Progressive.Power.Unit.Chain.Path
import Purelib.Data.Gaussian.Norm.Basic
import Purelib.Data.Rat.Fraction
import Purelib.Data.Rat.Fraction.Arithmetic
import Purelib.Data.Rat.Fraction.Order.Basic
import Purelib.Data.Rat.Interval.Basic
import Purelib.Geometry.Rational.Box.Basic
import Purelib.Polynomial.Dense.Gaussian.Basic
import Purelib.RootIsolation.Owner.Local.Basic
import Purelib.RootIsolation.Progressive.Chamber.Frame
import Purelib.RootIsolation.Progressive.Chamber.Path.Basic

open Purelib.Data

open Purelib

open Purelib.Geometry.Rational

open Purelib.Polynomial

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

namespace Purelib.RootIsolation.Power.Unit.Chain.Basic

open Purelib.Data.Gaussian
namespace UnitChain

/-- Parameter vertices synchronized with `liftVertices`; stationary repeats
record the two connector edges after each genuine parameter move. -/
@[expose] def liftParameterVertices
    {degree : Data.Nat.Positive.RootDegree} {degreeAtLeastTwo : 2 ≤ degree.value} :
    {start finish : Geometry.Gaussian.UnitCircle.Basic.UnitVertex} →
      Power.Unit.Chain.Basic.UnitChain degree degreeAtLeastTwo start finish → List Gaussian.Basic.Canonical
  | _, _, .nil _ => []
  | _, _, .cons (middle := middle) _ remaining =>
      Progressive.Power.Unit.Lift.Vertices.unitMoveParameterVertices middle.value ++
        remaining.liftParameterVertices
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

/-- The two stationary connector copies attached to every genuine parameter
move do not alter its coordinate winding. -/
theorem liftParameterRaw_eq_parameterRaw
    {degree : Data.Nat.Positive.RootDegree} {degreeAtLeastTwo : 2 ≤ degree.value} :
    ∀ {start finish : Geometry.Gaussian.UnitCircle.Basic.UnitVertex}
      (chain : Power.Unit.Chain.Basic.UnitChain degree degreeAtLeastTwo start finish),
      Winding.Polygon.Basic.chainRaw
          Dense.Gaussian.Monomial.Coordinate.coordinatePolynomial start.value
          chain.liftParameterVertices =
        Power.Unit.Chain.Basic.UnitChain.parameterRaw Dense.Gaussian.Monomial.Coordinate.coordinatePolynomial chain
  | _, _, .nil _ => rfl
  | source, finish, .cons (middle := middle) _ remaining => by
      simp only [-eq_self, -iff_self, Power.Unit.Chain.Basic.UnitChain.liftParameterVertices,
        Progressive.Power.Unit.Lift.Vertices.unitMoveParameterVertices,
        List.cons_append, List.nil_append, Winding.Polygon.Basic.chainRaw,
        Purelib.Polynomial.Winding.Polygon.Coordinate.coordinate_segment_self_doubledWinding,
        Int.Arithmetic.zero_add, Power.Unit.Chain.Basic.UnitChain.parameterRaw,
          Power.Unit.Chain.Basic.UnitChain.vertices]
      rw [Purelib.RootIsolation.Power.Unit.Chain.Basic.UnitChain.liftParameterRaw_eq_parameterRaw remaining]
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

/-- The synchronized parameter vertices terminate at the chain's exact finish parameter. -/
theorem liftParameterVertices_terminal
    {degree : Data.Nat.Positive.RootDegree} {degreeAtLeastTwo : 2 ≤ degree.value} :
    ∀ {start finish : Geometry.Gaussian.UnitCircle.Basic.UnitVertex}
      (chain : Power.Unit.Chain.Basic.UnitChain degree degreeAtLeastTwo start finish),
      Polygon.Chain.terminal start.value
          chain.liftParameterVertices = finish.value
  | _, _, .nil _ => rfl
  | source, finish, .cons (middle := middle) _ remaining => by
      rw [Power.Unit.Chain.Basic.UnitChain.liftParameterVertices, Polygon.Chain.terminal_append]
      change Polygon.Chain.terminal middle.value
        remaining.liftParameterVertices = finish.value
      exact Purelib.RootIsolation.Power.Unit.Chain.Basic.UnitChain.liftParameterVertices_terminal remaining
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

/-- For a closed unit chain, the synchronized parameter polygon has the
same raw winding as the underlying genuine parameter moves. -/
theorem closedLiftParameterRaw_eq_parameterRaw
    {degree : Data.Nat.Positive.RootDegree} {degreeAtLeastTwo : 2 ≤ degree.value}
    {vertex : Geometry.Gaussian.UnitCircle.Basic.UnitVertex}
    (chain : Power.Unit.Chain.Basic.UnitChain degree degreeAtLeastTwo vertex vertex) :
    Winding.Polygon.Basic.closedRaw Dense.Gaussian.Monomial.Coordinate.coordinatePolynomial
        vertex.value chain.liftParameterVertices =
      Power.Unit.Chain.Basic.UnitChain.parameterRaw Dense.Gaussian.Monomial.Coordinate.coordinatePolynomial chain := by
  unfold Winding.Polygon.Basic.closedRaw
  rw [Winding.Polygon.Basic.chainRaw_append,
    Power.Unit.Chain.Basic.UnitChain.liftParameterVertices_terminal]
  rw [Power.Unit.Chain.Basic.UnitChain.liftParameterRaw_eq_parameterRaw]
  simp only [-eq_self, -iff_self, Winding.Polygon.Basic.chainRaw,
    Winding.Polygon.Coordinate.coordinate_segment_self_doubledWinding,
    Int.add_zero]
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

/-- Rational lift vertices obtained by expanding every chamber move into its
three explicit connector edges. -/
@[expose] def liftVertices {degree : Data.Nat.Positive.RootDegree} {degreeAtLeastTwo : 2 ≤ degree.value} :
    {start finish : Geometry.Gaussian.UnitCircle.Basic.UnitVertex} →
      (chain : Power.Unit.Chain.Basic.UnitChain degree degreeAtLeastTwo start finish) →
      (start.frame degree degreeAtLeastTwo).Index → List Gaussian.Basic.Canonical
  | _, _, .nil _, _ => []
  | source, _, .cons (middle := middle) small remaining, index =>
      Progressive.Power.Unit.Lift.Vertices.unitMoveLiftVertices source.unit middle.unit degree degreeAtLeastTwo small
          index ++
        remaining.liftVertices
          ((Progressive.Power.Unit.Move.Path.unitSmallMovePath source.unit middle.unit degree degreeAtLeastTwo
            small).finalIndex index)
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

/-- The edgewise finite Rouché formulas telescope along an arbitrary finite
unit chain. -/
theorem liftHomotopy
    {degree : Data.Nat.Positive.RootDegree} {degreeAtLeastTwo : 2 ≤ degree.value} :
    ∀ {start finish : Geometry.Gaussian.UnitCircle.Basic.UnitVertex}
      (chain : Power.Unit.Chain.Basic.UnitChain degree degreeAtLeastTwo start finish)
      (index : (start.frame degree degreeAtLeastTwo).Index),
      Winding.Polygon.Comparison.ChainHomotopyFormula
        (Dense.Gaussian.Power.Coordinate.coordinatePositivePower (degree.value - 1))
        Dense.Gaussian.Monomial.Coordinate.coordinatePolynomial
        (start.ownerAnchor degree degreeAtLeastTwo index)
        (chain.liftVertices index) start.value chain.liftParameterVertices
  | _, _, .nil vertex, index => .nil (vertex.ownerAnchor degree
      degreeAtLeastTwo index) vertex.value
  | source, finish, .cons (middle := middle) small remaining, index => by
      let move := Progressive.Power.Unit.Move.Path.unitSmallMovePath source.unit middle.unit degree
        degreeAtLeastTwo small
      let nextIndex := move.finalIndex index
      have first := Progressive.Power.Unit.Lift.Formulas.unitMoveLiftHomotopy source.unit middle.unit degree
        degreeAtLeastTwo small index
      have tail := Purelib.RootIsolation.Power.Unit.Chain.Basic.UnitChain.liftHomotopy remaining nextIndex
      have liftEndpoint := Progressive.Power.Unit.Move.Path.unitMoveLift_terminal_eq_finalOwnerAnchor source.unit
        middle.unit degree degreeAtLeastTwo small index
      have liftEndpoint' : Polygon.Chain.terminal
          (Progressive.Power.Unit.Lift.Vertices.unitMoveLiftBase source.unit middle.unit degree degreeAtLeastTwo index)
          (Progressive.Power.Unit.Lift.Vertices.unitMoveLiftVertices source.unit middle.unit degree degreeAtLeastTwo
            small index) =
          middle.ownerAnchor degree degreeAtLeastTwo nextIndex := by
        simpa only [-eq_self, -iff_self, Geometry.Gaussian.UnitCircle.Basic.UnitVertex.ownerAnchor,
          Geometry.Gaussian.UnitCircle.Basic.UnitVertex.frame, move, nextIndex]
          using liftEndpoint
      rw [← liftEndpoint'] at tail
      have combined := first.append tail
      simpa only [-eq_self, -iff_self, Power.Unit.Chain.Basic.UnitChain.liftVertices,
        Power.Unit.Chain.Basic.UnitChain.liftParameterVertices,
        Geometry.Gaussian.UnitCircle.Basic.UnitVertex.ownerAnchor,
        Geometry.Gaussian.UnitCircle.Basic.UnitVertex.frame, Progressive.Power.Unit.Lift.Vertices.unitMoveLiftBase,
          move, nextIndex] using combined
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

/-- Constructive modulo-four phase data for every rational connector edge of
an arbitrary finite owner lift. -/
@[expose] def liftPhaseFormula
    {degree : Data.Nat.Positive.RootDegree} {degreeAtLeastTwo : 2 ≤ degree.value} :
    {start finish : Geometry.Gaussian.UnitCircle.Basic.UnitVertex} →
      (chain : Power.Unit.Chain.Basic.UnitChain degree degreeAtLeastTwo start finish) →
      (index : (start.frame degree degreeAtLeastTwo).Index) →
      Winding.Polygon.Phase.ChainPhaseFormula
        Dense.Gaussian.Monomial.Coordinate.coordinatePolynomial
        (start.ownerAnchor degree degreeAtLeastTwo index)
        (chain.liftVertices index)
  | _, _, .nil vertex, index =>
      Winding.Polygon.Phase.ChainPhaseFormula.nil
        Dense.Gaussian.Monomial.Coordinate.coordinatePolynomial
        (vertex.ownerAnchor degree degreeAtLeastTwo index)
  | source, finish, .cons (middle := middle) small remaining, index => by
      let move := Progressive.Power.Unit.Move.Path.unitSmallMovePath source.unit middle.unit degree
        degreeAtLeastTwo small
      let nextIndex := move.finalIndex index
      have first := Progressive.Power.Unit.Lift.Formulas.unitMoveLiftPhaseFormula source.unit middle.unit degree
        degreeAtLeastTwo small index
      have tail := Purelib.RootIsolation.Power.Unit.Chain.Basic.UnitChain.liftPhaseFormula remaining nextIndex
      have liftEndpoint := Progressive.Power.Unit.Move.Path.unitMoveLift_terminal_eq_finalOwnerAnchor source.unit
        middle.unit degree degreeAtLeastTwo small index
      have liftEndpoint' : Polygon.Chain.terminal
          (Progressive.Power.Unit.Lift.Vertices.unitMoveLiftBase source.unit middle.unit degree degreeAtLeastTwo index)
          (Progressive.Power.Unit.Lift.Vertices.unitMoveLiftVertices source.unit middle.unit degree degreeAtLeastTwo
            small index) =
          middle.ownerAnchor degree degreeAtLeastTwo nextIndex := by
        simpa only [-eq_self, -iff_self, Geometry.Gaussian.UnitCircle.Basic.UnitVertex.ownerAnchor,
          Geometry.Gaussian.UnitCircle.Basic.UnitVertex.frame, move, nextIndex]
          using liftEndpoint
      rw [← liftEndpoint'] at tail
      have combined := first.append tail
      simpa only [-eq_self, -iff_self, Power.Unit.Chain.Basic.UnitChain.liftVertices,
        Geometry.Gaussian.UnitCircle.Basic.UnitVertex.ownerAnchor, Geometry.Gaussian.UnitCircle.Basic.UnitVertex.frame,
        Progressive.Power.Unit.Lift.Vertices.unitMoveLiftBase, move, nextIndex] using combined
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

/-- Combine the original edgewise coordinate-power product formulas along the retained finite lifted chain. -/
theorem liftProductFormula
    {degree : Data.Nat.Positive.RootDegree} {degreeAtLeastTwo : 2 ≤ degree.value} :
    ∀ {start finish : Geometry.Gaussian.UnitCircle.Basic.UnitVertex}
      (chain : Power.Unit.Chain.Basic.UnitChain degree degreeAtLeastTwo start finish)
      (index : (start.frame degree degreeAtLeastTwo).Index)
      (exponent : Nat),
      Winding.Polygon.Product.ChainProductFormula
        (Dense.Gaussian.Power.Coordinate.coordinatePositivePower exponent)
        Dense.Gaussian.Monomial.Coordinate.coordinatePolynomial
        (start.ownerAnchor degree degreeAtLeastTwo index)
        (chain.liftVertices index)
  | _, _, .nil vertex, index, _ =>
      .nil (vertex.ownerAnchor degree degreeAtLeastTwo index)
  | source, finish, .cons (middle := middle) small remaining, index,
      exponent => by
      let move := Progressive.Power.Unit.Move.Path.unitSmallMovePath source.unit middle.unit degree
        degreeAtLeastTwo small
      let nextIndex := move.finalIndex index
      have first := Progressive.Power.Unit.Lift.Formulas.unitMoveLiftProductFormula source.unit middle.unit degree
        degreeAtLeastTwo small index exponent
      have tail := Purelib.RootIsolation.Power.Unit.Chain.Basic.UnitChain.liftProductFormula remaining nextIndex
        exponent
      have liftEndpoint := Progressive.Power.Unit.Move.Path.unitMoveLift_terminal_eq_finalOwnerAnchor source.unit
        middle.unit degree degreeAtLeastTwo small index
      have liftEndpoint' : Polygon.Chain.terminal
          (Progressive.Power.Unit.Lift.Vertices.unitMoveLiftBase source.unit middle.unit degree degreeAtLeastTwo index)
          (Progressive.Power.Unit.Lift.Vertices.unitMoveLiftVertices source.unit middle.unit degree degreeAtLeastTwo
            small index) =
          middle.ownerAnchor degree degreeAtLeastTwo nextIndex := by
        simpa only [-eq_self, -iff_self, Geometry.Gaussian.UnitCircle.Basic.UnitVertex.ownerAnchor,
          Geometry.Gaussian.UnitCircle.Basic.UnitVertex.frame, move, nextIndex]
          using liftEndpoint
      rw [← liftEndpoint'] at tail
      have combined := first.append tail
      simpa only [-eq_self, -iff_self, Power.Unit.Chain.Basic.UnitChain.liftVertices,
        Geometry.Gaussian.UnitCircle.Basic.UnitVertex.ownerAnchor, Geometry.Gaussian.UnitCircle.Basic.UnitVertex.frame,
        Progressive.Power.Unit.Lift.Vertices.unitMoveLiftBase, move, nextIndex] using combined
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

/-- Following the retained lifted vertices reaches the exact owner anchor selected by the chamber path's final index. -/
theorem liftVertices_terminal
    {degree : Data.Nat.Positive.RootDegree} {degreeAtLeastTwo : 2 ≤ degree.value} :
    ∀ {start finish : Geometry.Gaussian.UnitCircle.Basic.UnitVertex}
      (chain : Power.Unit.Chain.Basic.UnitChain degree degreeAtLeastTwo start finish)
      (index : (start.frame degree degreeAtLeastTwo).Index),
      Polygon.Chain.terminal
          (start.ownerAnchor degree degreeAtLeastTwo index)
          (chain.liftVertices index) =
        finish.ownerAnchor degree degreeAtLeastTwo
          (chain.toPath.finalIndex index)
  | _, _, .nil _, _ => rfl
  | source, finish, .cons (middle := middle) small remaining, index => by
      rw [Power.Unit.Chain.Basic.UnitChain.liftVertices, Polygon.Chain.terminal_append]
      rw [show source.ownerAnchor degree degreeAtLeastTwo index =
          Progressive.Power.Unit.Lift.Vertices.unitMoveLiftBase source.unit middle.unit degree degreeAtLeastTwo
            index by rfl]
      have moveEndpoint := Progressive.Power.Unit.Move.Path.unitMoveLift_terminal_eq_finalOwnerAnchor source.unit
        middle.unit degree degreeAtLeastTwo small index
      have moveEndpoint' : Polygon.Chain.terminal
          (Progressive.Power.Unit.Lift.Vertices.unitMoveLiftBase source.unit middle.unit degree degreeAtLeastTwo index)
          (Progressive.Power.Unit.Lift.Vertices.unitMoveLiftVertices source.unit middle.unit degree degreeAtLeastTwo
            small index) =
          middle.ownerAnchor degree degreeAtLeastTwo
            ((Progressive.Power.Unit.Move.Path.unitSmallMovePath source.unit middle.unit degree degreeAtLeastTwo
              small).finalIndex index) := by
        simpa only [-eq_self, -iff_self, Geometry.Gaussian.UnitCircle.Basic.UnitVertex.ownerAnchor,
          Geometry.Gaussian.UnitCircle.Basic.UnitVertex.frame] using moveEndpoint
      rw [moveEndpoint']
      rw [Purelib.RootIsolation.Power.Unit.Chain.Basic.UnitChain.liftVertices_terminal remaining
        ((Progressive.Power.Unit.Move.Path.unitSmallMovePath source.unit middle.unit degree degreeAtLeastTwo
          small).finalIndex index)]
      apply congrArg (finish.ownerAnchor degree degreeAtLeastTwo)
      exact (Progressive.Chamber.Path.Basic.ChamberPath.finalIndex_append
        (Progressive.Power.Unit.Move.Path.unitSmallMovePath source.unit middle.unit degree degreeAtLeastTwo small)
        remaining.toPath index).symm
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

/-- Close the original lifted-chain homotopy with its retained final segment when the owner index returns to its start.
-/
theorem closedHomotopyFormula_of_return
    {degree : Data.Nat.Positive.RootDegree} {degreeAtLeastTwo : 2 ≤ degree.value}
    {vertex : Geometry.Gaussian.UnitCircle.Basic.UnitVertex}
    (chain : Power.Unit.Chain.Basic.UnitChain degree degreeAtLeastTwo vertex vertex)
    (index : (vertex.frame degree degreeAtLeastTwo).Index)
    (returned : chain.toPath.finalIndex index = index) :
    Winding.Polygon.Comparison.ClosedHomotopyFormula
      (Dense.Gaussian.Power.Coordinate.coordinatePositivePower (degree.value - 1))
      Dense.Gaussian.Monomial.Coordinate.coordinatePolynomial
      (vertex.ownerAnchor degree degreeAtLeastTwo index)
      (chain.liftVertices index) vertex.value chain.liftParameterVertices := by
  let base := vertex.ownerAnchor degree degreeAtLeastTwo index
  let degreeIndex : Fin degree.value := Fin.cast
    (Progressive.Power.Unit.Frame.robustChamberFrame_degree (Gaussian.Norm.Nonzero.nonzero_of_normSq_eq_one vertex.unit)
      vertex.unit degree degreeAtLeastTwo) index
  have baseInside : (Power.Unit.Box.unitRobustBox (Gaussian.Norm.Nonzero.nonzero_of_normSq_eq_one vertex.unit)
      vertex.unit degree degreeAtLeastTwo degreeIndex).Contains base := by
    unfold base degreeIndex Geometry.Gaussian.UnitCircle.Basic.UnitVertex.ownerAnchor
      Geometry.Gaussian.UnitCircle.Basic.UnitVertex.frame
    rw [Progressive.Power.Unit.Frame.robustChamberFrame_owner_box]
    exact Box.contains_anchor _
  have openFormula := chain.liftHomotopy index
  have liftEndpoint := chain.liftVertices_terminal index
  rw [returned] at liftEndpoint
  have parameterEndpoint := chain.liftParameterVertices_terminal
  have finalEdge := Power.Unit.Segment.Homotopy.unitRobustSegmentHomotopy vertex.unit vertex.unit degree
    degreeAtLeastTwo (Power.Unit.Move.Budget.UnitMoveSmall.reflexive vertex.unit degree degreeAtLeastTwo)
    degreeIndex baseInside baseInside
  have tail : Winding.Polygon.Comparison.ChainHomotopyFormula
      (Dense.Gaussian.Power.Coordinate.coordinatePositivePower (degree.value - 1))
      Dense.Gaussian.Monomial.Coordinate.coordinatePolynomial
      (Polygon.Chain.terminal base (chain.liftVertices index)) [base]
      (Polygon.Chain.terminal vertex.value chain.liftParameterVertices)
      [vertex.value] := by
    rw [liftEndpoint, parameterEndpoint]
    exact .cons finalEdge (.nil base vertex.value)
  exact openFormula.append tail
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

/-- A returned owner lift has a fully constructed modulo-four phase
telescope, including its final rational segment back to the initial anchor. -/
@[expose] def closedPhaseFormula_of_return
    {degree : Data.Nat.Positive.RootDegree} {degreeAtLeastTwo : 2 ≤ degree.value}
    {vertex : Geometry.Gaussian.UnitCircle.Basic.UnitVertex}
    (chain : Power.Unit.Chain.Basic.UnitChain degree degreeAtLeastTwo vertex vertex)
    (index : (vertex.frame degree degreeAtLeastTwo).Index)
    (returned : chain.toPath.finalIndex index = index) :
    Winding.Polygon.Phase.ClosedPhaseFormula
      Dense.Gaussian.Monomial.Coordinate.coordinatePolynomial
      (vertex.ownerAnchor degree degreeAtLeastTwo index)
      (chain.liftVertices index) := by
  let base := vertex.ownerAnchor degree degreeAtLeastTwo index
  let degreeIndex : Fin degree.value := Fin.cast
    (Progressive.Power.Unit.Frame.robustChamberFrame_degree (Gaussian.Norm.Nonzero.nonzero_of_normSq_eq_one vertex.unit)
      vertex.unit degree degreeAtLeastTwo) index
  have baseInside : (Power.Unit.Box.unitRobustBox (Gaussian.Norm.Nonzero.nonzero_of_normSq_eq_one vertex.unit)
      vertex.unit degree degreeAtLeastTwo degreeIndex).Contains base := by
    unfold base degreeIndex Geometry.Gaussian.UnitCircle.Basic.UnitVertex.ownerAnchor
      Geometry.Gaussian.UnitCircle.Basic.UnitVertex.frame
    rw [Progressive.Power.Unit.Frame.robustChamberFrame_owner_box]
    exact Box.contains_anchor _
  have openFormula := chain.liftPhaseFormula index
  have endpoint := chain.liftVertices_terminal index
  rw [returned] at endpoint
  have finalCertificate : Clearance.Pair.Basic.Certificate
      (Dense.Gaussian.Path.Components.pathReal Dense.Gaussian.Monomial.Coordinate.coordinatePolynomial
        base (base - base))
      (Dense.Gaussian.Path.Components.pathImag Dense.Gaussian.Monomial.Coordinate.coordinatePolynomial
        base (base - base))
      { lower := 0, upper := 1, valid := by decide } := by
    simpa only [-eq_self, -iff_self, show Dense.Gaussian.Monomial.Coordinate.coordinatePolynomial =
        Dense.Gaussian.Power.Coordinate.coordinatePositivePower 0 from rfl] using
      Power.Unit.Segment.Clearance.unitRobustSegmentCoordinatePowerCertificate
        (Gaussian.Norm.Nonzero.nonzero_of_normSq_eq_one vertex.unit) vertex.unit degree
        degreeAtLeastTwo degreeIndex baseInside baseInside 0
  have tail : Winding.Polygon.Phase.ChainPhaseFormula
      Dense.Gaussian.Monomial.Coordinate.coordinatePolynomial
      (Polygon.Chain.terminal base (chain.liftVertices index)) [base] := by
    rw [endpoint]
    exact Winding.Polygon.Phase.ChainPhaseFormula.consOfClearance finalCertificate
      (Winding.Polygon.Phase.ChainPhaseFormula.nil
        Dense.Gaussian.Monomial.Coordinate.coordinatePolynomial base)
  exact openFormula.append tail
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

/-- Close the original coordinate-power product formulas using the retained final segment of a returned owner lift. -/
theorem closedProductFormula_of_return
    {degree : Data.Nat.Positive.RootDegree} {degreeAtLeastTwo : 2 ≤ degree.value}
    {vertex : Geometry.Gaussian.UnitCircle.Basic.UnitVertex}
    (chain : Power.Unit.Chain.Basic.UnitChain degree degreeAtLeastTwo vertex vertex)
    (index : (vertex.frame degree degreeAtLeastTwo).Index)
    (returned : chain.toPath.finalIndex index = index)
    (exponent : Nat) :
    Winding.Polygon.Product.ClosedProductFormula
      (Dense.Gaussian.Power.Coordinate.coordinatePositivePower exponent)
      Dense.Gaussian.Monomial.Coordinate.coordinatePolynomial
      (vertex.ownerAnchor degree degreeAtLeastTwo index)
      (chain.liftVertices index) := by
  let base := vertex.ownerAnchor degree degreeAtLeastTwo index
  let degreeIndex : Fin degree.value := Fin.cast
    (Progressive.Power.Unit.Frame.robustChamberFrame_degree (Gaussian.Norm.Nonzero.nonzero_of_normSq_eq_one vertex.unit)
      vertex.unit degree degreeAtLeastTwo) index
  have baseInside : (Power.Unit.Box.unitRobustBox (Gaussian.Norm.Nonzero.nonzero_of_normSq_eq_one vertex.unit)
      vertex.unit degree degreeAtLeastTwo degreeIndex).Contains base := by
    unfold base degreeIndex Geometry.Gaussian.UnitCircle.Basic.UnitVertex.ownerAnchor
      Geometry.Gaussian.UnitCircle.Basic.UnitVertex.frame
    rw [Progressive.Power.Unit.Frame.robustChamberFrame_owner_box]
    exact Box.contains_anchor _
  have openFormula := chain.liftProductFormula index exponent
  have endpoint := chain.liftVertices_terminal index
  rw [returned] at endpoint
  have finalEdge := Power.Unit.Segment.Product.unitRobustSegmentProductFormula
    (Gaussian.Norm.Nonzero.nonzero_of_normSq_eq_one vertex.unit) vertex.unit degree degreeAtLeastTwo
    degreeIndex baseInside baseInside exponent
  have tail : Winding.Polygon.Product.ChainProductFormula
      (Dense.Gaussian.Power.Coordinate.coordinatePositivePower exponent)
      Dense.Gaussian.Monomial.Coordinate.coordinatePolynomial
      (Polygon.Chain.terminal base (chain.liftVertices index)) [base] := by
    rw [endpoint]
    exact .cons finalEdge (.nil base)
  exact openFormula.append tail
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

/-- Assemble every finite positive-power winding formula for the original closed returned owner polygon. -/
theorem closedPositivePowerFormula_of_return
    {degree : Data.Nat.Positive.RootDegree} {degreeAtLeastTwo : 2 ≤ degree.value}
    {vertex : Geometry.Gaussian.UnitCircle.Basic.UnitVertex}
    (chain : Power.Unit.Chain.Basic.UnitChain degree degreeAtLeastTwo vertex vertex)
    (index : (vertex.frame degree degreeAtLeastTwo).Index)
    (returned : chain.toPath.finalIndex index = index) :
    (exponent : Nat) → Winding.Polygon.Power.ClosedPositivePowerFormula
      (vertex.ownerAnchor degree degreeAtLeastTwo index)
      (chain.liftVertices index) exponent
  | 0 => .zero
  | exponent + 1 => .succ
      (Purelib.RootIsolation.Power.Unit.Chain.Basic.UnitChain.closedPositivePowerFormula_of_return chain index returned
        exponent)
      (Power.Unit.Chain.Basic.UnitChain.closedProductFormula_of_return chain index returned exponent)

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

/-- Constructive normalization of a returned rational owner polygon. -/
@[expose] def normalizedLiftOfReturn
    {degree : Data.Nat.Positive.RootDegree} {degreeAtLeastTwo : 2 ≤ degree.value}
    {vertex : Geometry.Gaussian.UnitCircle.Basic.UnitVertex}
    (chain : Power.Unit.Chain.Basic.UnitChain degree degreeAtLeastTwo vertex vertex)
    (index : (vertex.frame degree degreeAtLeastTwo).Index)
    (returned : chain.toPath.finalIndex index = index) :
    Polynomial.Winding.Polygon.Normalized
      Dense.Gaussian.Monomial.Coordinate.coordinatePolynomial
      (vertex.ownerAnchor degree degreeAtLeastTwo index)
      (chain.liftVertices index) :=
  Polynomial.Winding.Polygon.Normalized.ofPhaseFormula _ _ _
    (Power.Unit.Chain.Basic.UnitChain.closedPhaseFormula_of_return chain index returned)
end UnitChain
end Purelib.RootIsolation.Power.Unit.Chain.Basic

end
