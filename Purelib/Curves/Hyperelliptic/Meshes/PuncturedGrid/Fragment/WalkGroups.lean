module
import Purelib.Data.List.Map
import Purelib.Data.List.Append
import Purelib.RootIsolation.SquareRoot.Grid.Walk
import Purelib.Data.Gaussian.Basic
import Purelib.Data.Rat.Fraction
import Purelib.Approximation.Gaussian.Equivalence
import Purelib.Approximation.Gaussian.Name.Basic
import Purelib.Curves.Hyperelliptic.Basic
import Purelib.Curves.Hyperelliptic.Differentials.Basic
import Purelib.Data.Gaussian.Norm.Sum.Basic
import Purelib.Geometry.Rational.Box.Basic
import Purelib.Polynomial.Geometry.ClearPath

import Purelib.Curves.Hyperelliptic.Branches.BranchIsolation
import Purelib.Curves.Hyperelliptic.Meshes.PuncturedGrid.Face.CommonMeshes
import Purelib.Curves.Hyperelliptic.Meshes.PuncturedGrid.Face.DomainBanks
import Purelib.Curves.Hyperelliptic.Meshes.PuncturedGrid.Face.MeshWords
import Purelib.Curves.Hyperelliptic.Meshes.PuncturedGrid.Face.PrimitiveData
import Purelib.Curves.Hyperelliptic.Meshes.PuncturedGrid.Fragment.RootedWords
import Purelib.Curves.Hyperelliptic.Meshes.PuncturedGrid.Fragment.RouteContacts
import Purelib.Curves.Hyperelliptic.Meshes.PuncturedGrid.Fragment.RouteWords
public import Purelib.Curves.Hyperelliptic.Meshes.PuncturedGrid.Fragment.SourceGeometry
import Purelib.Curves.Hyperelliptic.Meshes.PuncturedGrid.MeshPathWalks
import Purelib.Curves.Hyperelliptic.Meshes.PuncturedGrid.PreparedPrimitiveSplits
import Purelib.Curves.Hyperelliptic.Meshes.PuncturedGrid.SkeletonFaceAssignments
import Purelib.Polynomial.Geometry.Grid.Walks
import Purelib.Riemann.Meshes.FramedPuncturedGrid
import Purelib.Riemann.Meshes.GridLiftedMesh
import Purelib.Riemann.Paths.OwnerTraceReadings
import Purelib.Riemann.Paths.PreparedSegmentSources
import Purelib.RootIsolation.SquareRoot.Grid.LiftedVertices
import Purelib.RootIsolation.SquareRoot.Grid.RootEdgeBank
import Purelib.RootIsolation.SquareRoot.Grid.RootFrames
import Purelib.Curves.Hyperelliptic.Meshes.PuncturedGrid.Fragment.RouteEndpoints
import Purelib.Curves.Hyperelliptic.Meshes.PuncturedGrid.Fragment.GroupOwners
import Init.Prelude
import Purelib.Curves.Hyperelliptic.Branches.BranchCellBank
import Purelib.Curves.Hyperelliptic.Branches.Cuts
import Purelib.Curves.Hyperelliptic.Branches.FramedBranchCellBank
import Purelib.Curves.Hyperelliptic.Meshes.PuncturedGrid.WalkFaceAssignments
import Purelib.Data.Gaussian.Field
import Purelib.Polynomial.Dense.Basic
import Purelib.Polynomial.Dense.Evaluation
import Purelib.Riemann.Meshes.PuncturedGridFaces
import Purelib.Topology.Polygon.Stokes
import Purelib.Tactic.Ring
meta import Mathlib.Tactic.Linter.Lint

public section

/-! Fold complete original rooted groups over the actual standard grid walk.
Each step returns the owner used by the next stored edge transition. -/

section

open Purelib
open Purelib.Approximation
open Purelib.Curves.Hyperelliptic.Meshes.PuncturedGrid
open Purelib.Curves.Hyperelliptic.Meshes.PuncturedGrid.Face
open Purelib.Curves.Hyperelliptic.Meshes.PuncturedGrid.Face.MeshWords
open Purelib.Curves.Hyperelliptic.Meshes.PuncturedGrid.Fragment
open Purelib.Curves.Hyperelliptic.Meshes.PuncturedGrid.Fragment.GroupOwners
open Purelib.Curves.Hyperelliptic.Meshes.PuncturedGrid.Fragment.RootedWords
open Purelib.Curves.Hyperelliptic.Meshes.PuncturedGrid.Fragment.RouteEndpoints
open Purelib.Curves.Hyperelliptic.Meshes.PuncturedGrid.MeshPathWalks
open Purelib.Geometry
open Purelib.Polynomial.Geometry
open Purelib.Polynomial.Geometry.Grid
open Purelib.Riemann.Paths
open Purelib.RootIsolation.SquareRoot.Grid.EdgeBank

open Purelib.Data.List

open Purelib.Curves.Hyperelliptic.Basic (HyperellipticCurve)
open Purelib.Curves.Hyperelliptic.Differentials.Basic (Differential)
open Purelib.Data.Gaussian.Basic renaming Canonical -> Gaussian
open Purelib.Data.Rat.Fraction (Rational)
open Purelib.Polynomial.Geometry.ClearPath (ClearSegment)
open Purelib.Curves.Hyperelliptic.Branches (BranchCellBank)
open Purelib.Riemann.Meshes (FramedPuncturedGrid)
open Purelib.Curves.Hyperelliptic.Meshes.PuncturedGrid.PreparedPrimitiveSplits (PrimitiveAxes)
open Purelib.Curves.Hyperelliptic.Meshes.PuncturedGrid.Face.DomainBanks (FaceDomainBank)
open Purelib.Riemann.Meshes.GridLiftedMesh (LiftedMesh)
open Purelib.Curves.Hyperelliptic.Meshes.PuncturedGrid.Fragment.RootedWords (LiftedFragment)
open Purelib.Curves.Hyperelliptic.Meshes.PuncturedGrid.Fragment.RootedWords.LiftedFragment (RootedWord)
open Purelib.Curves.Hyperelliptic.Meshes.PuncturedGrid.Fragment.SourceGeometry (Presents)
open Purelib.Curves.Hyperelliptic.Meshes.PuncturedGrid.Face.CommonMeshes (FaceMeshBudgets FaceSharedMeshes)
open Purelib.Curves.Hyperelliptic.Meshes.PuncturedGrid.Face.PrimitiveData (FacePrimitiveBank)
open Purelib.Curves.Hyperelliptic.Meshes.PuncturedGrid.Fragment.RouteWords (canonicalRoute)
open Purelib.Curves.Hyperelliptic.Meshes.PuncturedGrid.Fragment.RouteContacts (routeValue)
open Purelib.Riemann.Paths.OwnerTraceReadings (ownerName)
open Purelib.Approximation.Gaussian.Equivalence (NamedEquivalent)
open Purelib.Approximation.Gaussian.Name.Basic (Named)
open _root_.Purelib.Data.Gaussian.Norm.Sum.Basic (gaussianSum)
open Purelib.Riemann.Paths.PreparedSegmentSources (SegmentSource)

variable {genus : Nat} {curve : HyperellipticCurve genus} {branches :
  Purelib.Curves.Hyperelliptic.Branches.BranchIsolation.Data curve}
  {higher : 1 < curve.polynomial.natDegree} {base : FramedPuncturedGrid curve branches higher}
  {frames : RootIsolation.SquareRoot.Grid.RootFrames base.bank.grid} {vertices :
    Purelib.RootIsolation.SquareRoot.Grid.LiftedVertices.VertexBank base.bank.grid} {edges :
    Purelib.RootIsolation.SquareRoot.Grid.RootEdgeBank frames}
  {source : Differential genus} {axes :
    PrimitiveAxes base.bank.grid}
  {domains : FaceDomainBank frames
    base.faces.regulars} {mesh : LiftedMesh vertices edges base.faces}
  {count : Nat} {target : Rational}

namespace Purelib.Curves.Hyperelliptic.Meshes.PuncturedGrid.Fragment

/-- Exact nonempty fragment blocks on the retained grid-walk edges, with original segment ancestry and root names at
every group boundary. -/
inductive WalkGroups : {first last : Data.Gaussian.Basic.Canonical} → Walks.Walk base.bank.grid first last →
  Gaussian.Name.Basic.Named → Gaussian.Name.Basic.Named →
    List (RootedWords.LiftedFragment axes domains mesh source count target) → Prop
  /-- An empty original walk retains root equivalence between its two endpoint names. -/ | nil {point :
    Data.Gaussian.Basic.Canonical} {firstName lastName : Gaussian.Name.Basic.Named} (root : Nonempty
    (Gaussian.Equivalence.NamedEquivalent firstName lastName)) :
      WalkGroups (.nil point) firstName lastName
        []
  /-- Append one actual nonempty rooted source group on the retained grid edge, preserving source ancestry, movement,
    geometry and the outgoing root. -/ | cons {first middle last : Data.Gaussian.Basic.Canonical} {edge : Walks.Edge
    base.bank.grid first middle}
      {tail : Walks.Walk base.bank.grid middle last} {firstName middleName lastName : Gaussian.Name.Basic.Named}
      {head : RootedWords.LiftedFragment axes domains mesh source count target}
      {block pieces : List (RootedWords.LiftedFragment axes domains mesh source count target)}
      {ambient : Rational.Box} {start finish : Data.Gaussian.Basic.Canonical} {segment :
        ClearPath.ClearSegment curve.polynomial ambient start finish}
      (word : LiftedFragment.RootedWord (head :: block) first firstName middle middleName)
      (original : ∀ piece ∈ head :: block, PreparedSegmentSources.SegmentSource segment piece.parent)
      (moving : ∀ piece ∈ head :: block, piece.last ≠ piece.first)
      (geometry : ∀ piece ∈ head :: block, SourceGeometry.Presents piece first middle)
      (remaining : WalkGroups tail middleName
        lastName pieces) :
      WalkGroups (.cons edge tail) firstName
        lastName ((head :: block) ++ pieces)

end Purelib.Curves.Hyperelliptic.Meshes.PuncturedGrid.Fragment

namespace Purelib.Curves.Hyperelliptic.Meshes.PuncturedGrid.Fragment.WalkGroups

/-- Preserve actual group order and the original intermediate root when joining segment or tour legs. -/
theorem append {first middle last : Data.Gaussian.Basic.Canonical} {left : Walks.Walk base.bank.grid first middle}
    {right : Walks.Walk base.bank.grid middle last} {firstName middleName lastName : Gaussian.Name.Basic.Named}
    {before after : List (RootedWords.LiftedFragment axes domains mesh source count target)}
    (leftGroups : WalkGroups left firstName middleName
      before) (rightGroups : WalkGroups right middleName
      lastName after) :
    WalkGroups (left.append right) firstName lastName
      (before ++ after) := by
  induction leftGroups with
  | nil root =>
      obtain ⟨root⟩ := root
      cases rightGroups with
      | nil lastRoot =>
          obtain ⟨lastRoot⟩ := lastRoot
          exact .nil ⟨root.trans lastRoot⟩
      | cons word original moving geometry rest =>
          exact .cons (word.changeStart rfl ⟨root⟩) original moving geometry rest
  | cons word original moving geometry remaining ih =>
      rw [Append.append_assoc]
      exact .cons word original moving geometry (ih rightGroups)

end Purelib.Curves.Hyperelliptic.Meshes.PuncturedGrid.Fragment.WalkGroups

variable {points : List Purelib.Data.Gaussian.Basic.Canonical} {tolerance : Rational} {index :
  Nat}
  {budgets : FaceMeshBudgets source points tolerance
    domains} {numerics : FacePrimitiveBank source
    index domains}

namespace Purelib.Curves.Hyperelliptic.Meshes.PuncturedGrid.Fragment.WalkGroups

/-- The finite Gaussian sum of an appended original list is the sum of its two retained list totals. -/
private theorem sum_append (first last : List Data.Gaussian.Basic.Canonical) :
  Data.Gaussian.Norm.Sum.Basic.gaussianSum (first ++ last) = Data.Gaussian.Norm.Sum.Basic.gaussianSum first +
  Data.Gaussian.Norm.Sum.Basic.gaussianSum last := by
  induction first with
  | nil => exact (zero_add _).symm
  | cons head tail ih =>
    change head + Data.Gaussian.Norm.Sum.Basic.gaussianSum (tail ++ last) = (head +
      Data.Gaussian.Norm.Sum.Basic.gaussianSum tail) + Data.Gaussian.Norm.Sum.Basic.gaussianSum last; rw [ih];
      ring1

/-- The actual retained walk-face values split into their first original edge increment and the remaining walk values.
-/
private theorem walk_values_cons {first middle last : Data.Gaussian.Basic.Canonical}
    (edge : Walks.Edge base.bank.grid first middle) (tail : Walks.Walk base.bank.grid middle last)
    (sheet : Fin 2) (shared : CommonMeshes.FaceSharedMeshes budgets numerics) :
    (SkeletonFaceAssignments.walkFaces mesh (.cons edge tail) sheet).values (fun _ route =>
      FaceSharedMeshes.edgeIncrement shared route) =
      FaceSharedMeshes.edgeIncrement shared (EdgeRoute.build mesh (edges.indexedEdge vertices edge sheet)
        (SkeletonFaceAssignments.indexedEdge_supported mesh edge sheet)) ::
      (SkeletonFaceAssignments.walkFaces mesh tail ((edges.edge edge).forward.target sheet)).values
        (fun _ route => FaceSharedMeshes.edgeIncrement shared route) := rfl

/-- The full value fold and its outgoing root use the same cached edge transitions as the actual standard walk-face
assignment. -/
theorem read {first last : Data.Gaussian.Basic.Canonical} {walk : Walks.Walk base.bank.grid first last}
    {firstName lastName : Gaussian.Name.Basic.Named} {pieces : List (RootedWords.LiftedFragment axes domains mesh source
      count target)}
    (groups : WalkGroups walk firstName lastName pieces)
    (vertex : Fin vertices.count) (coordinate : vertices.coordinate vertex = first)
    (root : Gaussian.Equivalence.NamedEquivalent (OwnerTraceReadings.ownerName (vertices.owner frames vertex))
      firstName)
    (shared : CommonMeshes.FaceSharedMeshes budgets numerics) :
    ∃ finalVertex : Fin vertices.count, vertices.coordinate finalVertex = last ∧
      vertices.sheet finalVertex = RootEdgeBank.target edges walk (vertices.sheet vertex) ∧
      Nonempty (Gaussian.Equivalence.NamedEquivalent (OwnerTraceReadings.ownerName (vertices.owner frames finalVertex))
        lastName) ∧
      Data.Gaussian.Norm.Sum.Basic.gaussianSum (pieces.map (fun piece => RouteContacts.routeValue piece
        (RouteWords.canonicalRoute piece) shared)) =
        Data.Gaussian.Norm.Sum.Basic.gaussianSum ((SkeletonFaceAssignments.walkFaces mesh walk (vertices.sheet
          vertex)).values
          (fun _ route => FaceSharedMeshes.edgeIncrement shared route)) := by
  induction groups generalizing vertex with
  | nil equivalent =>
      obtain ⟨equivalent⟩ := equivalent
      exact ⟨vertex, coordinate, rfl, ⟨root.trans equivalent⟩, rfl⟩
  | @cons first middle last edge tail firstName middleName lastName head block pieces ambient start finish segment word
    original moving geometry remaining ih =>
      let next := (edges.indexedEdge vertices edge (vertices.sheet vertex)).finish
      have nextCoordinate : vertices.coordinate next = middle := vertices.coordinate_index _ edge.vertices.2 _
      have nextSheet : vertices.sheet next = (edges.edge edge).forward.target (vertices.sheet vertex) :=
        vertices.sheet_index _ edge.vertices.2 _
      obtain ⟨nextRoot⟩ := RootedWord.routed_finish_owner word geometry edge vertex coordinate root
      have increment := RootedWord.routed_increment word original moving geometry edge vertex coordinate root shared
      obtain ⟨finalVertex, finalCoordinate, finalSheet, finalRoot, tailSum⟩ := ih next nextCoordinate nextRoot
      refine ⟨finalVertex, finalCoordinate, ?_, finalRoot, ?_⟩
      · exact finalSheet.trans (congrArg (RootEdgeBank.target edges tail) nextSheet)
      · rw [Map.map_append, sum_append,
          increment, tailSum,
          walk_values_cons, nextSheet]
        rfl

end Purelib.Curves.Hyperelliptic.Meshes.PuncturedGrid.Fragment.WalkGroups

end
