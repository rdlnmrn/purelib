module
meta import Purelib.Elab.ConstructiveInjectivity
import Purelib.Riemann.Integration.PreparedSubdivisionModelCore
import Purelib.Riemann.Integration.RectangularPrimitiveGluing
import Purelib.Riemann.Integration.RectangularPrimitiveModels
import Purelib.Riemann.Normalization.InverseRootPolynomial
import Purelib.Riemann.Normalization.RectangularInverseModels
import Purelib.Curves.Hyperelliptic.Basic
import Purelib.Curves.Hyperelliptic.Differentials.Basic
import Purelib.Data.Rat.Fraction.Order.Arithmetic
import Purelib.Data.Vector.Basic

import Purelib.Geometry.Rectangle.Partition.PreparedSegmentCuts
import Purelib.LinearAlgebra.Grid.Offsets
public import Purelib.Riemann.Integration.RectangularPairedPointBanks
import Purelib.Riemann.Integration.PreparedParentSplitting
import Purelib.Riemann.Paths.RectangularPairedSegments
import Purelib.Riemann.Readings.RectangularPointReadings
import Purelib.Tactic.Ring

public section

/-! Reexpress an existing physical trace in one original parent parameter.
Only the finite parameter vector is computed. Owners and primitive readings
are retained without evaluating the source or grid models again. -/
open Purelib.Riemann.Normalization.RectangularInverseModels (Geometry)
namespace Purelib.Riemann.Paths.RectangularTraceParameterReadings
open Purelib.Riemann.Normalization.InverseRootPolynomial (Coordinate Gaussian Polynomial)
open Purelib.Curves.Hyperelliptic.Basic (HyperellipticCurve)
open Purelib.Curves.Hyperelliptic.Differentials.Basic (Differential)
open Purelib.Riemann.Integration.PreparedSubdivisionModelCore (CenteredEdge)
open Purelib.Riemann.Paths.RectangularPairedSegments (PairedSegmentPiece)
open Purelib.Riemann.Integration.RectangularPairedPointBanks (Trace)
open Purelib.Riemann.Normalization.RectangularInverseModels (Bank)
open Purelib.Riemann.Integration.RectangularPrimitiveModels (Primitives)
open Purelib.Riemann.Integration.RectangularPrimitiveGluing (PrimitiveAnchors)
open Purelib.Riemann.Readings.RectangularPointReadings (PointReadings)
open Purelib.Riemann.Integration.PreparedParentSplitting (prepared_point_eq)
open Purelib.Data.Vector.Basic (vectorOfFn vectorOfFn_apply)
open Purelib.Data.Rat.Fraction.Compatibility
variable {leftColumns leftRows rightColumns rightRows count genus : Nat}
  {leftGeometry : Geometry leftColumns leftRows} {rightGeometry : Geometry rightColumns rightRows}
  {piece : PairedSegmentPiece leftGeometry rightGeometry}
  {curve : Purelib.Curves.Hyperelliptic.Basic.HyperellipticCurve genus} {differential :
    Purelib.Curves.Hyperelliptic.Differentials.Basic.Differential genus}

open Purelib.Data in
set_option genInjectivity false in
/-- Retain one physical trace in the parameters of its original parent edge.

The finite parameter vector is linked both to the affine rescaling of the original trace and to its exact physical
points. -/
structure ParentParameters (trace : Trace piece count) (parent : CenteredEdge curve differential)
    (first last : Coordinate) where
  /-- The cached trace parameters in the original parent interval. -/ parameters : Data.Vector Coordinate (count
    + 1)
  /-- Each parent parameter is the affine rescaling of the original trace parameter. -/ parameters_eq : ∀ vertex,
    parameters vertex = first + trace.parameters vertex * (last - first)
  /-- The original trace points are exactly the parent-edge points at the cached parameters. -/ point_eq : ∀ vertex,
    trace.points vertex = parent.edge.point (parameters vertex)

constructive_injectivity ParentParameters

open Purelib.Data in
open Purelib.Geometry in
/-- Compute the parameter vector from exact endpoint identifications.

The construction preserves the physical trace and its original parent, using the affine segment equation to certify
every cached parameter. -/
@[expose] def ParentParameters.build (trace : Trace piece count) (parent : CenteredEdge curve differential)
    (first last : Coordinate) (firstEq : piece.first = parent.edge.point first) (lastEq : piece.last = parent.edge.point
      last) :
    ParentParameters trace parent first last :=
  let parameters := Vector.Basic.vectorOfFn (fun vertex => first + trace.parameters vertex * (last - first))
  { parameters := parameters
    parameters_eq := fun vertex => Vector.Basic.vectorOfFn_apply _ vertex
    point_eq := by
      intro vertex
      dsimp only [parameters]
      rw [Vector.Basic.vectorOfFn_apply, trace.points_eq, firstEq, lastEq, ←
        Rectangle.Partition.PreparedSegmentCuts.point_eq_line]
      have affine := Rectangle.Partition.PreparedSegmentCuts.point_affine (parent.edge.point 0) (parent.edge.point 1)
        first last (trace.parameters vertex)
      rw [← prepared_point_eq parent first, ← prepared_point_eq parent last,
        ← prepared_point_eq parent (first + trace.parameters vertex * (last - first))] at affine
      exact affine.symm }

namespace ParentParameters
variable {trace : Trace piece count} {parent : CenteredEdge curve differential} {first last : Coordinate}

/-- The last cached parent parameter is the supplied interval endpoint. -/
theorem last_parameter (transport : ParentParameters trace parent first last) :
    transport.parameters (Fin.last count) = last := by
  rw [transport.parameters_eq, trace.last_eq]
  ring1

/-- The trace's last physical point is the original parent point at the supplied final parameter. -/
theorem last_point (transport : ParentParameters trace parent first last) : piece.last = parent.edge.point last :=
  trace.last_point.symm.trans ((transport.point_eq (Fin.last count)).trans
    (congrArg parent.edge.point transport.last_parameter))

section
open Purelib.Data
/-- For a forward parent interval, every cached parameter lies between its endpoints. -/
theorem inside (transport : ParentParameters trace parent first last) (ordered : first ≤ last) (vertex : Fin (count +
  1)) :
    first ≤ transport.parameters vertex ∧ transport.parameters vertex ≤ last := by
  rw [transport.parameters_eq]
  have width := Rat.Fraction.Order.Arithmetic.sub_nonneg_direct ordered
  constructor
  · exact le_add_of_nonneg_right (Rat.Fraction.Order.Arithmetic.mul_nonneg_direct (trace.within vertex).1 width)
  · exact (Rat.Fraction.Order.Arithmetic.add_le_add_direct (le_refl first)
      (Rat.Fraction.Order.Arithmetic.mul_le_mul_of_nonneg_right_direct (trace.within vertex).2 width)).trans_eq (by
        ring1)

/-- Increasing trace parameters remain increasing under a forward parent parametrization. -/
theorem ordered (transport : ParentParameters trace parent first last) (direction : first ≤ last)
    (increasing : ∀ edge : Fin count, trace.parameters edge.castSucc ≤ trace.parameters edge.succ)
    (edge : Fin count) : transport.parameters edge.castSucc ≤ transport.parameters edge.succ := by
  rw [transport.parameters_eq, transport.parameters_eq]
  exact Rat.Fraction.Order.Arithmetic.add_le_add_direct le_rfl
    (Rat.Fraction.Order.Arithmetic.mul_le_mul_of_nonneg_right_direct (increasing edge)
    (Rat.Fraction.Order.Arithmetic.sub_nonneg_direct direction))

/-- Every cached reversed parameter lies between its original endpoints.

The retained trace parameter lies in the unit interval. Its complementary
parameter scales the original nonnegative reversed width without changing
the cached affine point. -/
theorem inside_reverse (transport : ParentParameters trace parent first last) (direction : last ≤ first)
    (vertex : Fin (count + 1)) : last ≤ transport.parameters vertex ∧ transport.parameters vertex ≤ first := by
  rw [transport.parameters_eq]
  have width := Rat.Fraction.Order.Arithmetic.sub_nonneg_direct direction
  constructor
  · exact (le_add_of_nonneg_right
      (Rat.Fraction.Order.Arithmetic.mul_nonneg_direct (Rat.Fraction.Order.Arithmetic.sub_nonneg_direct (trace.within
        vertex).2) width)).trans_eq (by ring1)
  · have upper := Rat.Fraction.Order.Arithmetic.add_le_add_direct (le_refl last)
      (Rat.Fraction.Order.Arithmetic.mul_le_mul_of_nonneg_right_direct
        ((Rat.Fraction.Order.Arithmetic.sub_le_sub_left_direct (trace.within vertex).1 (1 : Coordinate)).trans_eq (show
        (1 : Coordinate) - 0 = 1 by ring1)) width)
    have leftEq : last + (1 - trace.parameters vertex) * (first - last) =
        first + trace.parameters vertex * (last - first) := by ring1
    rw [leftEq] at upper
    exact upper.trans_eq (by ring1)

/-- Increasing trace parameters decrease under the original reversed parametrization.

Subtracting each retained parameter from one reverses their scalar ordering.
Multiplication by the original nonnegative width transports that ordering to
the same cached parent parameters. -/
theorem ordered_reverse (transport : ParentParameters trace parent first last) (direction : last ≤ first)
    (increasing : ∀ edge : Fin count, trace.parameters edge.castSucc ≤ trace.parameters edge.succ)
    (edge : Fin count) : transport.parameters edge.succ ≤ transport.parameters edge.castSucc := by
  rw [transport.parameters_eq, transport.parameters_eq]
  have upper := Rat.Fraction.Order.Arithmetic.add_le_add_direct (le_refl last)
    (Rat.Fraction.Order.Arithmetic.mul_le_mul_of_nonneg_right_direct
      (Rat.Fraction.Order.Arithmetic.sub_le_sub_left_direct (increasing edge) (1 : Coordinate))
      (Rat.Fraction.Order.Arithmetic.sub_nonneg_direct direction))
  have affine (parameter : Coordinate) : last + (1 - parameter) * (first - last) = first + parameter * (last - first) :=
    by ring1
  rw [affine, affine] at upper
  exact upper

end

open Purelib.LinearAlgebra
/-- Transport retained point readings to the exact parent parametrization.

The original owner and value caches are reused, changing only the physical-point equality evidence. -/
@[expose] def readings (transport : ParentParameters trace parent first last)
    {polynomial numerator : Polynomial} {columns rows : Nat} {geometry : Geometry columns rows}
    {models : Bank polynomial geometry} {primitives : Primitives models numerator}
    {anchors : PrimitiveAnchors primitives} {offsets : LinearAlgebra.Grid.Offsets anchors.edges}
    (original : PointReadings anchors offsets (fun vertex => trace.points vertex)) :
    PointReadings anchors offsets (fun vertex => parent.edge.point (transport.parameters vertex)) :=
  ⟨original.owners, fun vertex => (original.point_eq vertex).trans (transport.point_eq vertex), original.values,
    original.value_eq⟩

/-- Transport preserves every cached numerical point reading definitionally. -/
theorem readings_value (transport : ParentParameters trace parent first last)
    {polynomial numerator : Polynomial} {columns rows : Nat} {geometry : Geometry columns rows}
    {models : Bank polynomial geometry} {primitives : Primitives models numerator}
    {anchors : PrimitiveAnchors primitives} {offsets : LinearAlgebra.Grid.Offsets anchors.edges}
    (original : PointReadings anchors offsets (fun vertex => trace.points vertex)) (vertex : Fin (count + 1)) :
    (transport.readings original).values vertex = original.values vertex := rfl

end ParentParameters
end Purelib.Riemann.Paths.RectangularTraceParameterReadings
