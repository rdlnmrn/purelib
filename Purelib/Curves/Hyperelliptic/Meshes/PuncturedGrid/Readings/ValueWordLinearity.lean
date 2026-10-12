module
import Purelib.Algebra.FiniteSum.Gaussian
import Purelib.Data.Gaussian.Cast
import Purelib.Curves.Hyperelliptic.Basic
import Purelib.Data.Gaussian.Basic
import Purelib.Data.List.Flatten

import Purelib.Curves.Hyperelliptic.Meshes.PuncturedGrid.CanonicalEdgeValues
import Purelib.Data.List.Permutation
import Purelib.Topology.Surface.Sewing.PrimitiveSewing
import Purelib.Topology.Surface.Sewing.SewingRetraction
import Purelib.Curves.Hyperelliptic.Meshes.PuncturedGrid.OwnedPuncturedMesh

public import Purelib.Curves.Hyperelliptic.Meshes.PuncturedGrid.Readings.EdgeMagnitude
import Purelib.Curves.Hyperelliptic.Branches.BranchCellBank
import Purelib.Curves.Hyperelliptic.Branches.Cuts
import Purelib.Curves.Hyperelliptic.Branches.FramedBranchCellBank
import Purelib.Riemann.Meshes.FramedPuncturedGrid
import Purelib.Riemann.Meshes.GridLiftedMesh
import Purelib.Riemann.Meshes.LiftedPuncturedGrid
import Purelib.RootIsolation.SquareRoot.Grid.LiftedVertices
import Purelib.Topology.Polygon.Stokes
import Purelib.Tactic.Ring

open Purelib.Curves

open Purelib.Data

open Purelib

public section

/-!
# Conjugate-linearity of word values under a mixed value vector

The mixed-value API needs the word value and the signed face correction of a
mixed value vector to be the conjugate-linear combination of the two sides.
This module proves the word-level and face-level linearity, reducing the
per-edge support obligation to the retained triangle boundary.
-/

namespace Purelib.Curves.Hyperelliptic.Meshes.PuncturedGrid.Readings.ValueWordLinearity

open Purelib.Curves.Hyperelliptic.Meshes.PuncturedGrid (OwnedPuncturedMesh)

open Purelib.Topology.Polygon.Stokes (OrientedEdge OrientedTriangle triangleEdgeOccurrences)

open Purelib.Curves.Hyperelliptic.Meshes.PuncturedGrid.Readings.EdgeMagnitude

variable {genus : Nat} {curve : Hyperelliptic.Basic.HyperellipticCurve genus}
  {owner : OwnedPuncturedMesh curve}

/-- Every triangle boundary edge is a retained triangle occurrence. -/
theorem OrientedTriangle.boundary_mem_triangleEdgeOccurrences {faceCount : Nat}
    {triangles : Fin faceCount → OrientedTriangle owner.vertices.count} (index : Fin faceCount)
    {edge : OrientedEdge owner.vertices.count} (member : edge ∈ (triangles index).boundary) :
    edge ∈ triangleEdgeOccurrences triangles :=
  Data.List.Flatten.mem_flatMap.mpr
    ⟨triangles index, Data.List.Permutation.ofFn_mem triangles index, member⟩

/-- The word value of a mixed value vector is the conjugate-linear combination
of the two sides, on any supported word. -/
theorem wordValue_mixValues {leftValues rightValues : Fin owner.mesh.triangles.length →
  Topology.Surface.Sewing.PrimitiveSewing.PrimitiveValues 3}
    (coefficient : Gaussian.Basic.Canonical) (source : List (OrientedEdge owner.vertices.count))
    (supported : ∀ edge ∈ source, edge ∈ triangleEdgeOccurrences owner.mesh.triangulation.faces ∨
      edge.reverse ∈ triangleEdgeOccurrences owner.mesh.triangulation.faces) :
    Topology.Surface.Sewing.SewingRetraction.wordValue
        (Hyperelliptic.Meshes.PuncturedGrid.CanonicalEdgeValues.edgeValuation owner.mesh (EdgeMagnitude.mixValues (owner
          := owner) leftValues rightValues coefficient))
        source =
      Gaussian.Basic.conj (Topology.Surface.Sewing.SewingRetraction.wordValue
        (Hyperelliptic.Meshes.PuncturedGrid.CanonicalEdgeValues.edgeValuation owner.mesh leftValues) source) +
        coefficient * Topology.Surface.Sewing.SewingRetraction.wordValue
          (Hyperelliptic.Meshes.PuncturedGrid.CanonicalEdgeValues.edgeValuation owner.mesh rightValues) source := by
  induction source with
  | nil =>
      change (0 : Gaussian.Basic.Canonical) = Gaussian.Basic.conj 0 + coefficient * 0
      rw [Gaussian.Basic.conj_zero, mul_zero, add_zero]
  | cons edge rest inductionHypothesis =>
      change
        Hyperelliptic.Meshes.PuncturedGrid.CanonicalEdgeValues.edgeValuation owner.mesh
            (EdgeMagnitude.mixValues (owner := owner) leftValues rightValues coefficient) edge +
          Topology.Surface.Sewing.SewingRetraction.wordValue
            (Hyperelliptic.Meshes.PuncturedGrid.CanonicalEdgeValues.edgeValuation owner.mesh
            (EdgeMagnitude.mixValues (owner := owner) leftValues rightValues coefficient)) rest =
        Gaussian.Basic.conj (Hyperelliptic.Meshes.PuncturedGrid.CanonicalEdgeValues.edgeValuation owner.mesh
          leftValues edge +
          Topology.Surface.Sewing.SewingRetraction.wordValue
            (Hyperelliptic.Meshes.PuncturedGrid.CanonicalEdgeValues.edgeValuation owner.mesh leftValues) rest) +
        coefficient * (Hyperelliptic.Meshes.PuncturedGrid.CanonicalEdgeValues.edgeValuation owner.mesh rightValues edge
          +
          Topology.Surface.Sewing.SewingRetraction.wordValue
            (Hyperelliptic.Meshes.PuncturedGrid.CanonicalEdgeValues.edgeValuation owner.mesh rightValues) rest)
      rw [EdgeMagnitude.edgeValuation_mixValues (owner := owner) coefficient (supported edge List.mem_cons_self),
        inductionHypothesis (fun next member => supported next (List.mem_cons_of_mem _ member)),
        Gaussian.Basic.conj_add]
      ring1

/-- The signed face correction of a mixed value vector is the conjugate-linear
combination of the two sides. -/
theorem faceValue_mixValues
    (correction : List (Topology.Surface.Sewing.SewingRetraction.FaceTerm owner.mesh.triangles.length))
    {leftValues rightValues : Fin owner.mesh.triangles.length → Topology.Surface.Sewing.PrimitiveSewing.PrimitiveValues
      3} (coefficient : Gaussian.Basic.Canonical) :
    Topology.Surface.Sewing.SewingRetraction.faceValue owner.mesh.triangulation.faces
        (Hyperelliptic.Meshes.PuncturedGrid.CanonicalEdgeValues.edgeValuation owner.mesh (EdgeMagnitude.mixValues (owner
          := owner) leftValues rightValues coefficient))
        correction =
      Gaussian.Basic.conj (Topology.Surface.Sewing.SewingRetraction.faceValue owner.mesh.triangulation.faces
        (Hyperelliptic.Meshes.PuncturedGrid.CanonicalEdgeValues.edgeValuation owner.mesh leftValues) correction) +
        coefficient * Topology.Surface.Sewing.SewingRetraction.faceValue owner.mesh.triangulation.faces
          (Hyperelliptic.Meshes.PuncturedGrid.CanonicalEdgeValues.edgeValuation owner.mesh rightValues) correction := by
  induction correction with
  | nil =>
      change (0 : Gaussian.Basic.Canonical) = Gaussian.Basic.conj 0 + coefficient * 0
      rw [Gaussian.Basic.conj_zero, mul_zero, add_zero]
  | cons term rest inductionHypothesis =>
      change (term.1 : Gaussian.Basic.Canonical) * Topology.Surface.Sewing.SewingRetraction.wordValue
            (Hyperelliptic.Meshes.PuncturedGrid.CanonicalEdgeValues.edgeValuation owner.mesh (EdgeMagnitude.mixValues
              (owner := owner) leftValues rightValues coefficient))
            (owner.mesh.triangulation.faces term.2).boundary +
          Topology.Surface.Sewing.SewingRetraction.faceValue owner.mesh.triangulation.faces
            (Hyperelliptic.Meshes.PuncturedGrid.CanonicalEdgeValues.edgeValuation owner.mesh (EdgeMagnitude.mixValues
              (owner := owner) leftValues rightValues coefficient))
            rest =
        Gaussian.Basic.conj ((term.1 : Gaussian.Basic.Canonical) *
          Topology.Surface.Sewing.SewingRetraction.wordValue
          (Hyperelliptic.Meshes.PuncturedGrid.CanonicalEdgeValues.edgeValuation owner.mesh leftValues)
            (owner.mesh.triangulation.faces term.2).boundary +
          Topology.Surface.Sewing.SewingRetraction.faceValue owner.mesh.triangulation.faces
            (Hyperelliptic.Meshes.PuncturedGrid.CanonicalEdgeValues.edgeValuation owner.mesh leftValues) rest) +
        coefficient * ((term.1 : Gaussian.Basic.Canonical) * Topology.Surface.Sewing.SewingRetraction.wordValue
          (Hyperelliptic.Meshes.PuncturedGrid.CanonicalEdgeValues.edgeValuation owner.mesh rightValues)
            (owner.mesh.triangulation.faces term.2).boundary +
          Topology.Surface.Sewing.SewingRetraction.faceValue owner.mesh.triangulation.faces
            (Hyperelliptic.Meshes.PuncturedGrid.CanonicalEdgeValues.edgeValuation owner.mesh rightValues) rest)
      rw [wordValue_mixValues coefficient (owner.mesh.triangulation.faces term.2).boundary
          (fun edge member => Or.inl
            (OrientedTriangle.boundary_mem_triangleEdgeOccurrences term.2 member)),
        inductionHypothesis, Gaussian.Basic.conj_add, Gaussian.Basic.conj_mul, Data.Gaussian.Cast.conj_intCast]
      ring1

end Purelib.Curves.Hyperelliptic.Meshes.PuncturedGrid.Readings.ValueWordLinearity

namespace Purelib.Curves.Hyperelliptic.Meshes.PuncturedGrid.Readings.ValueWordLinearity

open Purelib.Curves.Hyperelliptic.Meshes.PuncturedGrid (OwnedPuncturedMesh)

open Purelib.Topology.Polygon.Stokes (OrientedEdge OrientedTriangle triangleEdgeOccurrences)

open Purelib.Curves.Hyperelliptic.Meshes.PuncturedGrid.Readings.EdgeMagnitude

variable {genus : Nat} {curve : Hyperelliptic.Basic.HyperellipticCurve genus}
  {owner : OwnedPuncturedMesh curve}

/-- The whole retained triangle-occurrence word is supported. -/
theorem wordValue_mixValues_triangles
    {leftValues rightValues : Fin owner.mesh.triangles.length → Topology.Surface.Sewing.PrimitiveSewing.PrimitiveValues
      3} (coefficient : Gaussian.Basic.Canonical) :
    Topology.Surface.Sewing.SewingRetraction.wordValue
      (Hyperelliptic.Meshes.PuncturedGrid.CanonicalEdgeValues.edgeValuation owner.mesh
        (EdgeMagnitude.mixValues (owner := owner) leftValues rightValues coefficient))
        (triangleEdgeOccurrences owner.mesh.triangulation.faces) =
      Gaussian.Basic.conj (Topology.Surface.Sewing.SewingRetraction.wordValue
        (Hyperelliptic.Meshes.PuncturedGrid.CanonicalEdgeValues.edgeValuation owner.mesh leftValues)
        (triangleEdgeOccurrences owner.mesh.triangulation.faces)) +
        coefficient * Topology.Surface.Sewing.SewingRetraction.wordValue
          (Hyperelliptic.Meshes.PuncturedGrid.CanonicalEdgeValues.edgeValuation owner.mesh rightValues)
          (triangleEdgeOccurrences owner.mesh.triangulation.faces) :=
  wordValue_mixValues coefficient _ (fun _ member => Or.inl member)

end Purelib.Curves.Hyperelliptic.Meshes.PuncturedGrid.Readings.ValueWordLinearity
