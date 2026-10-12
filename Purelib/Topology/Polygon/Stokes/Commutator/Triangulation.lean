module
import Purelib.Data.Gaussian.Basic
public import Purelib.Integration.Energy.AffineTriangle
import Purelib.Topology.Polygon.Stokes
import Purelib.Data.Rat.Fraction
import Purelib.Tactic.Ring

open Purelib.Data

open Purelib.Integration.Energy

open Purelib.Topology.Polygon

open Purelib.Topology.Polygon.Stokes

section
@[expose] public section

/-!
# Triangulated finite surface energy

This module supplies the two-dimensional algebraic bridge for the second
Riemann bilinear relation.  A finite sample consists of a genuine oriented
triangulation, primitive values at its vertices, an exact identification of
its outer boundary with the displayed A/B period commutators, and a checked
lower-energy inequality on every face.  Incidence cancellation and finite
summation then derive the global surface lower theorem consumed by
`PreparedEnergy`; it is not repeated as an assumption.
-/

namespace Purelib.Topology.Polygon.Stokes.Commutator.Triangulation

/-! ## Canonical genus-one cut polygon -/

/-- The displayed oriented edge from vertex 0 to vertex 1 of the commutator square. -/
public def commutatorEdge01 :
    Stokes.OrientedEdge 4 := ⟨0, 1⟩

/-- The displayed oriented edge from vertex 1 to vertex 2 of the commutator square. -/
public def commutatorEdge12 :
    Stokes.OrientedEdge 4 := ⟨1, 2⟩

/-- The displayed oriented edge from vertex 2 to vertex 0 of the commutator square. -/
public def commutatorEdge20 :
    Stokes.OrientedEdge 4 := ⟨2, 0⟩

/-- The displayed oriented edge from vertex 0 to vertex 2 of the commutator square. -/
public def commutatorEdge02 :
    Stokes.OrientedEdge 4 := ⟨0, 2⟩

/-- The displayed oriented edge from vertex 2 to vertex 3 of the commutator square. -/
public def commutatorEdge23 :
    Stokes.OrientedEdge 4 := ⟨2, 3⟩

/-- The displayed oriented edge from vertex 3 to vertex 0 of the commutator square. -/
public def commutatorEdge30 :
    Stokes.OrientedEdge 4 := ⟨3, 0⟩

/-- The two counterclockwise triangles of the standard commutator square. The second triangle is written cyclically as
`(2,3,0)`, making its outer edges literal while retaining the same diagonal as `(0,2,3)`. -/
def genusOneCommutatorFaces (face : Fin 2) :
    Stokes.OrientedTriangle 4 :=
  if face = 0 then ⟨0, 1, 2⟩ else ⟨2, 3, 0⟩

section
open Purelib.Topology.Polygon.Stokes.Commutator
/-- The first retained commutator triangle has vertices 0, 1, 2.

This is the first original triangle of the displayed two-face table, with its ordered vertices unchanged. -/
@[simp] theorem genusOneCommutatorFaces_zero :
    Triangulation.genusOneCommutatorFaces 0 = ⟨0, 1, 2⟩ := by
  simp only [Triangulation.genusOneCommutatorFaces, -eq_self, -iff_self]
  rfl

/-- The second retained commutator triangle has vertices 2, 3, 0.

This is the second original triangle of the displayed two-face table, with its cyclic orientation unchanged. -/
@[simp] theorem genusOneCommutatorFaces_one :
    Triangulation.genusOneCommutatorFaces 1 = ⟨2, 3, 0⟩ := by
  simp only [Triangulation.genusOneCommutatorFaces, if_neg (by decide : (1 : Fin 2) ≠ 0), -eq_self, -iff_self]
  rfl

/-- Exact two-face triangulation of `0,a,a+b,b`. Its sole internal diagonal occurs as `(2,0)` and `(0,2)`; the incidence
proof explicitly moves that pair behind the four outer commutator edges. -/
def genusOneCommutatorTriangulation :
    Stokes.Triangulation 4 2 where
  faces := Triangulation.genusOneCommutatorFaces
  boundary :=
    [Triangulation.commutatorEdge01, Triangulation.commutatorEdge12,
      Triangulation.commutatorEdge23, Triangulation.commutatorEdge30]
  internalEdges := [Triangulation.commutatorEdge20]
  incidence := by
    change Stokes.EdgeReordering
      [Triangulation.commutatorEdge01, Triangulation.commutatorEdge12,
        Triangulation.commutatorEdge20,
        Triangulation.commutatorEdge23, Triangulation.commutatorEdge30,
          Triangulation.commutatorEdge02]
      [Triangulation.commutatorEdge01, Triangulation.commutatorEdge12,
        Triangulation.commutatorEdge23,
        Triangulation.commutatorEdge30, Triangulation.commutatorEdge20,
          Triangulation.commutatorEdge02]
    exact .cons Triangulation.commutatorEdge01 (.cons Triangulation.commutatorEdge12
      (.trans
        (.swap Triangulation.commutatorEdge20 Triangulation.commutatorEdge23
          [Triangulation.commutatorEdge30, Triangulation.commutatorEdge02])
        (.cons Triangulation.commutatorEdge23
          (.swap Triangulation.commutatorEdge20 Triangulation.commutatorEdge30
            [Triangulation.commutatorEdge02]))))

end

/-- Primitive vertices of the standard cut polygon, in boundary order `0,a,a+b,b`. -/
def genusOneCommutatorPrimitive (a b :
  Stokes.PrimitivePoint) (vertex : Fin 4) :
    Stokes.PrimitivePoint :=
  if vertex = 0 then PrimitivePoint.zero
  else if vertex = 1 then a
  else if vertex = 2 then a.add b
  else b

open Purelib.Topology.Polygon.Stokes.Commutator
/-- The first commutator vertex has zero primitive values.

The original four-vertex parameterization starts at the zero primitive point. -/
@[simp] theorem genusOneCommutatorPrimitive_zero (a b :
  Stokes.PrimitivePoint) :
    Triangulation.genusOneCommutatorPrimitive a b 0 =
      PrimitivePoint.zero := by
  simp only [Triangulation.genusOneCommutatorPrimitive, -eq_self, -iff_self]
  rfl

/-- The second commutator vertex has primitive increment a.

The original four-vertex parameterization reads its first supplied primitive increment at this index. -/
@[simp] theorem genusOneCommutatorPrimitive_one (a b :
  Stokes.PrimitivePoint) :
    Triangulation.genusOneCommutatorPrimitive a b 1 = a := by
  simp only [Triangulation.genusOneCommutatorPrimitive,
    if_neg (by decide : (1 : Fin 4) ≠ 0), -eq_self, -iff_self]
  rfl

/-- The third commutator vertex has primitive increment a plus b.

The original four-vertex parameterization retains the ordered sum of the two supplied primitive increments. -/
@[simp] theorem genusOneCommutatorPrimitive_two (a b :
  Stokes.PrimitivePoint) :
    Triangulation.genusOneCommutatorPrimitive a b 2 = a.add b := by
  simp only [Triangulation.genusOneCommutatorPrimitive,
    if_neg (by decide : (2 : Fin 4) ≠ 0),
    if_neg (by decide : (2 : Fin 4) ≠ 1), -eq_self, -iff_self]
  rfl

/-- The fourth commutator vertex has primitive increment b.

The original four-vertex parameterization ends at the second supplied primitive increment. -/
@[simp] theorem genusOneCommutatorPrimitive_three (a b :
  Stokes.PrimitivePoint) :
    Triangulation.genusOneCommutatorPrimitive a b 3 = b := by
  simp only [Triangulation.genusOneCommutatorPrimitive,
    if_neg (by decide : (3 : Fin 4) ≠ 0),
    if_neg (by decide : (3 : Fin 4) ≠ 1),
    if_neg (by decide : (3 : Fin 4) ≠ 2), -eq_self, -iff_self]
  rfl

/-- The explicit triangulation's outer boundary is definitionally the standard genus-one commutator boundary. -/
theorem genusOneCommutatorTriangulation_boundaryArea
    (a b : Stokes.PrimitivePoint) :
    Stokes.edgeListArea
        (Triangulation.genusOneCommutatorPrimitive a b)
        Triangulation.genusOneCommutatorTriangulation.boundary =
      Stokes.commutatorBoundaryArea
        PrimitivePoint.zero a b := by
  unfold Triangulation.genusOneCommutatorTriangulation
    Stokes.commutatorBoundaryArea
    Stokes.commutatorVertices
    Triangulation.commutatorEdge01 Triangulation.commutatorEdge12 Triangulation.commutatorEdge23
      Triangulation.commutatorEdge30
  simp only [Stokes.edgeListArea,
    Stokes.polygonBoundaryArea,
    Stokes.pathToAnchorArea,
    Triangulation.genusOneCommutatorPrimitive_zero,
    Triangulation.genusOneCommutatorPrimitive_one, Triangulation.genusOneCommutatorPrimitive_two,
    Triangulation.genusOneCommutatorPrimitive_three]
  unfold Stokes.edgeArea
    PrimitivePoint.zero
    PrimitivePoint.add
  dsimp only
  ring1

/-- The first face of the explicit commutator mesh is the triangle `(0,a,a+b)`. -/
@[simp] theorem genusOneCommutatorFirstFaceEnergy
    (a b : Stokes.PrimitivePoint) :
    AffineTriangle.triangleEnergy (Triangulation.genusOneCommutatorPrimitive a b)
        (Triangulation.genusOneCommutatorTriangulation.faces 0) =
      AffineTriangle.primitiveTriangleEnergy
        PrimitivePoint.zero a (a.add b) := by
  unfold Triangulation.genusOneCommutatorTriangulation
  change AffineTriangle.triangleEnergy (Triangulation.genusOneCommutatorPrimitive a b)
    (Triangulation.genusOneCommutatorFaces 0) = _
  rw [Triangulation.genusOneCommutatorFaces_zero]
  unfold AffineTriangle.triangleEnergy AffineTriangle.primitiveTriangleEnergy
  rw [Triangulation.genusOneCommutatorPrimitive_zero,
    Triangulation.genusOneCommutatorPrimitive_one, Triangulation.genusOneCommutatorPrimitive_two]

/-- The cyclically written second face has the same energy as the triangle `(0,a+b,b)`. -/
@[simp] theorem genusOneCommutatorSecondFaceEnergy
    (a b : Stokes.PrimitivePoint) :
    AffineTriangle.triangleEnergy (Triangulation.genusOneCommutatorPrimitive a b)
        (Triangulation.genusOneCommutatorTriangulation.faces 1) =
      AffineTriangle.primitiveTriangleEnergy
        PrimitivePoint.zero (a.add b) b := by
  unfold Triangulation.genusOneCommutatorTriangulation
  change AffineTriangle.triangleEnergy (Triangulation.genusOneCommutatorPrimitive a b)
    (Triangulation.genusOneCommutatorFaces 1) = _
  rw [Triangulation.genusOneCommutatorFaces_one]
  unfold AffineTriangle.triangleEnergy AffineTriangle.primitiveTriangleEnergy
  rw [Triangulation.genusOneCommutatorPrimitive_two,
    Triangulation.genusOneCommutatorPrimitive_three, Triangulation.genusOneCommutatorPrimitive_zero]
  apply congrArg (fun value : Gaussian.Basic.Canonical => value.im / 4)
  unfold Stokes.triangleWedgeArea
    PrimitivePoint.zero
    PrimitivePoint.add
  dsimp only
  ring1

end Purelib.Topology.Polygon.Stokes.Commutator.Triangulation

end
