module

public import Purelib.Topology.Mesh.QuadrilateralDual
public import Purelib.Topology.Surface.Sewing.SewingRetraction.Comparison
import Purelib.Topology.Mesh.IndexedQuadrilaterals
import Purelib.Data.Gaussian.Field
import Purelib.Tactic.Ring

/-! # Signed face terms at an actual retained quadrilateral occurrence

The two original bounded triangle indices supply the face terms. Their
actual incidence exposes the quadrilateral boundary and both orientations
of its diagonal; antisymmetric readings cancel that diagonal alone.
-/

public section

namespace Purelib.Topology.Mesh.QuadrilateralDual.QuadOccurrence

open Purelib
open Purelib.Data.Gaussian.Basic (Canonical)
open Purelib.Topology.Mesh.IndexedQuadrilaterals (IndexedQuadrilateral)
open Purelib.Topology.Polygon.Stokes (OrientedEdge OrientedTriangle pairedEdgeOccurrences)
open Purelib.Topology.Surface.Sewing

variable {vertices faceCount : Nat} {faces : Fin faceCount → OrientedTriangle vertices}
variable {quad : IndexedQuadrilateral vertices}

/-- The two original triangle positions, each with multiplicity one, in the retained subdivision order. -/
@[expose] def faceTerms (located : QuadOccurrence faces quad) : List (SewingRetraction.FaceTerm faceCount) :=
  [(1, located.first), (1, located.second)]

/-- The original incidence and antisymmetry remove exactly the paired diagonal from a quadrilateral subdivision. -/
private theorem subdivision_value (quad : IndexedQuadrilateral vertices)
    (value : OrientedEdge vertices → Canonical) (anti : ∀ edge, value edge.reverse = -value edge) :
    SewingRetraction.wordValue value quad.firstTriangle.boundary +
      SewingRetraction.wordValue value quad.secondTriangle.boundary =
        SewingRetraction.wordValue value quad.boundary := by
  have incidence := SewingRetraction.wordValue_reordering value quad.incidence
  have subdivision : SewingRetraction.wordValue value (quad.triangles.flatMap OrientedTriangle.boundary) =
      SewingRetraction.wordValue value quad.firstTriangle.boundary +
        SewingRetraction.wordValue value quad.secondTriangle.boundary :=
    SewingRetraction.wordValue_append value quad.firstTriangle.boundary quad.secondTriangle.boundary
  have diagonal : SewingRetraction.wordValue value (pairedEdgeOccurrences [quad.diagonal]) = 0 := by
    change value quad.diagonal + (value quad.diagonal.reverse + 0) = 0
    rewrite [anti quad.diagonal]
    ring1
  exact subdivision.symm.trans (incidence.trans
    ((SewingRetraction.wordValue_append value quad.boundary (pairedEdgeOccurrences [quad.diagonal])).trans
      ((congrArg (SewingRetraction.wordValue value quad.boundary + ·) diagonal).trans
        (Data.Gaussian.Basic.add_zero _))))

/-- The face terms read the actual quadrilateral boundary using its original two face equations and incidence. -/
theorem faceTerms_value (located : QuadOccurrence faces quad) (value : OrientedEdge vertices → Canonical)
    (anti : ∀ edge, value edge.reverse = -value edge) :
    SewingRetraction.faceValue faces value located.faceTerms = SewingRetraction.wordValue value quad.boundary := by
  change (1 : Canonical) * SewingRetraction.wordValue value (faces located.first).boundary +
      ((1 : Canonical) * SewingRetraction.wordValue value (faces located.second).boundary + 0) = _
  rewrite [located.first_eq, located.second_eq, Data.Gaussian.Basic.one_mul,
    Data.Gaussian.Basic.one_mul, Data.Gaussian.Basic.add_zero]
  exact subdivision_value quad value anti

end Purelib.Topology.Mesh.QuadrilateralDual.QuadOccurrence
