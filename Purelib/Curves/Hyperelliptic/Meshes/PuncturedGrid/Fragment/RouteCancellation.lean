module
import Purelib.Riemann.Integration.RectangularSharedPrimitives

import Purelib.Polynomial.Dense.Gaussian.Basic
import Purelib.Data.Gaussian.Basic
import Purelib.Data.Rat.Fraction
import Purelib.Approximation.Gaussian.Equivalence
import Purelib.Approximation.Gaussian.Name.Basic
import Purelib.Curves.Hyperelliptic.Basic
import Purelib.Curves.Hyperelliptic.Differentials.Basic
import Purelib.Data.Gaussian.Norm.Sum.Basic

import Purelib.Curves.Hyperelliptic.Branches.BranchIsolation
import Purelib.Curves.Hyperelliptic.Meshes.PuncturedGrid.Face.CommonMeshes
import Purelib.Curves.Hyperelliptic.Meshes.PuncturedGrid.Face.DomainBanks
import Purelib.Curves.Hyperelliptic.Meshes.PuncturedGrid.Face.MeshWords
import Purelib.Curves.Hyperelliptic.Meshes.PuncturedGrid.Face.PrimitiveData
import Purelib.Curves.Hyperelliptic.Meshes.PuncturedGrid.Fragment.RootedWords
import Purelib.Curves.Hyperelliptic.Meshes.PuncturedGrid.Fragment.RouteContacts
public import Purelib.Curves.Hyperelliptic.Meshes.PuncturedGrid.Fragment.WordJunctions
import Purelib.Curves.Hyperelliptic.Meshes.PuncturedGrid.PreparedPrimitiveSplits
import Purelib.Riemann.Meshes.FramedPuncturedGrid
import Purelib.Riemann.Meshes.GridLiftedMesh
import Purelib.Riemann.Readings.RectangularPrimitiveBoundary
import Purelib.RootIsolation.SquareRoot.Grid.LiftedVertices
import Purelib.RootIsolation.SquareRoot.Grid.RootEdgeBank
import Purelib.RootIsolation.SquareRoot.Grid.RootFrames
import Purelib.Topology.Polygon.Stokes
public import Purelib.Curves.Hyperelliptic.Meshes.PuncturedGrid.Fragment.RouteWords
import Purelib.Curves.Hyperelliptic.Branches.BranchCellBank
import Purelib.Curves.Hyperelliptic.Branches.Cuts
import Purelib.Curves.Hyperelliptic.Branches.FramedBranchCellBank
import Purelib.Curves.Hyperelliptic.Meshes.PuncturedGrid.Face.Entries
import Purelib.Curves.Hyperelliptic.Meshes.PuncturedGrid.Face.InverseModels
import Purelib.Curves.Hyperelliptic.Meshes.PuncturedGrid.Face.Periods
import Purelib.Curves.Hyperelliptic.Meshes.PuncturedGrid.Fragment.LiftedEdges
import Purelib.Curves.Hyperelliptic.Meshes.PuncturedGrid.Fragment.RegularFaces
import Purelib.Curves.Hyperelliptic.Meshes.PuncturedGrid.Fragment.SheetEntries
import Purelib.Curves.Hyperelliptic.Meshes.PuncturedGrid.MeshEdgeContainment
import Purelib.Curves.Hyperelliptic.Meshes.PuncturedGrid.PreparedFragmentCells
import Purelib.Data.Gaussian.Field
import Purelib.Data.Vector.Basic
import Purelib.Geometry.Rational.Box.Sample
import Purelib.Geometry.Rectangle.Partition.RectangularCommonMesh
import Purelib.Polynomial.Dense.Basic
import Purelib.Polynomial.Dense.Evaluation
import Purelib.Polynomial.Geometry.Grid.ClearGrid
import Purelib.Polynomial.Geometry.Grid.EdgeSides
import Purelib.Riemann.Branches.RectangularSheetGauge
import Purelib.Riemann.Integration.RectangularRefinementSigns
import Purelib.Riemann.Meshes.PuncturedEdgeFaces
import Purelib.Riemann.Meshes.PuncturedFaceLookup
import Purelib.Riemann.Meshes.PuncturedGridFaces
import Purelib.Riemann.Meshes.RectangularFaceModels
import Purelib.Riemann.Normalization.ContinuedInverseRoot
import Purelib.Riemann.Normalization.RectangularInverseModels
import Purelib.Riemann.Paths.OwnerTraceReadings
import Purelib.Riemann.Readings.PreparedPrimitiveSamples
import Purelib.Riemann.Readings.RectangularExteriorBoundary
import Purelib.Riemann.Readings.UniformPreparedRequests
import Purelib.Riemann.RootContinuation.RootOwnerFrames
import Purelib.Riemann.Topology.SquareRootContinuationChain
import Purelib.Tactic.Ring
import Purelib.Curves.Hyperelliptic.Meshes.PuncturedGrid.Fragment.JunctionSheets

public section

/-!
# Cancellation of actual partial readings on one lifted edge

Repeated containing edges share a route only after both root occurrence and
traversal direction have been identified. The resulting telescope reads the
original cached endpoint values, without replacing partial increments by
complete edges before the endpoint conditions have been proved.
-/

section

open Purelib.Approximation
open Purelib.Curves
open Purelib.Data
open Purelib.Data.Rat
open Purelib.Riemann
open Purelib.RootIsolation
open Purelib

open Purelib.Data.Gaussian.Basic renaming Canonical -> Gaussian

open Purelib.Polynomial.Dense.Gaussian.Basic.CanonicalCoefficients (CoefficientPolynomial)

variable {numerator : CoefficientPolynomial}

variable {genus : Nat} {curve : Hyperelliptic.Basic.HyperellipticCurve genus} {branches :
  Hyperelliptic.Branches.BranchIsolation.Data curve}
  {higher : 1 < curve.polynomial.natDegree} {base : Meshes.FramedPuncturedGrid curve branches higher}
  {frames : SquareRoot.Grid.RootFrames base.bank.grid} {vertices :
      SquareRoot.Grid.LiftedVertices.VertexBank
    base.bank.grid} {edges : SquareRoot.Grid.RootEdgeBank frames}
  {source : Hyperelliptic.Differentials.Basic.Differential genus} {axes :
    Hyperelliptic.Meshes.PuncturedGrid.PreparedPrimitiveSplits.PrimitiveAxes base.bank.grid}
  {domains : Hyperelliptic.Meshes.PuncturedGrid.Face.DomainBanks.FaceDomainBank frames base.faces.regulars} {mesh :
    Meshes.GridLiftedMesh.LiftedMesh vertices edges base.faces}
  {count : Nat} {target : Fraction.Rational}
  {points : List Gaussian.Basic.Canonical} {tolerance : Fraction.Rational} {index : Nat}
  {budgets : Hyperelliptic.Meshes.PuncturedGrid.Face.CommonMeshes.FaceMeshBudgets source points tolerance
    (numerator := numerator) domains}
    {numerics : Hyperelliptic.Meshes.PuncturedGrid.Face.PrimitiveData.FacePrimitiveBank source index
      (numerator := numerator) domains}

open Purelib.Riemann.Integration.RectangularSharedPrimitives renaming SharedPrimitiveValues -> SharedValues

namespace Purelib.Curves.Hyperelliptic.Meshes.PuncturedGrid.Fragment.RouteCancellation

/-- A point reading in the exact route selected for this occurrence. -/
@[expose] def canonicalPoint (piece : RootedWords.LiftedFragment axes
  domains mesh source count target)
    (shared : Face.CommonMeshes.FaceSharedMeshes budgets numerics) (point :
      Gaussian.Basic.Canonical) : Gaussian :=
  SharedValues.atPoint
    ((Face.MeshWords.FaceSharedMeshes.atRoute shared
      (RouteWords.canonicalRoute piece)).atSheet
      (RouteWords.canonicalRoute piece).sheet).readings point

/-- The actual selected-route increment is its cached final point reading minus its cached initial reading. -/
theorem routeValue_eq (piece : RootedWords.LiftedFragment axes domains mesh
  source count target)
    (shared : Face.CommonMeshes.FaceSharedMeshes budgets numerics) :
    (RouteContacts.routeValue piece)
      (RouteWords.canonicalRoute piece) shared =
      (RouteCancellation.canonicalPoint piece) shared piece.last -
      (RouteCancellation.canonicalPoint piece) shared piece.first := rfl

/-- Equal original lifted edges and lookup directions identify their actual cached point reading. -/
private theorem directed_point_eq
    {left right : Topology.Polygon.Stokes.OrientedEdge vertices.count}
    (leftSupported : left ∈ Topology.Polygon.Stokes.triangleEdgeOccurrences mesh.triangulation.faces ∨
      left.reverse ∈ Topology.Polygon.Stokes.triangleEdgeOccurrences mesh.triangulation.faces)
    (rightSupported : right ∈ Topology.Polygon.Stokes.triangleEdgeOccurrences mesh.triangulation.faces ∨
      right.reverse ∈ Topology.Polygon.Stokes.triangleEdgeOccurrences mesh.triangulation.faces)
    {first last : Bool} (edgeEq : left = right) (directionEq : first = last)
    (shared : Face.CommonMeshes.FaceSharedMeshes budgets numerics) (point :
      Gaussian.Basic.Canonical) :
    SharedValues.atPoint
      ((Face.MeshWords.FaceSharedMeshes.atRoute shared
        (RouteWords.directedRoute mesh left leftSupported first)).atSheet
        (RouteWords.directedRoute mesh left leftSupported
          first).sheet).readings point =
    SharedValues.atPoint
      ((Face.MeshWords.FaceSharedMeshes.atRoute shared
        (RouteWords.directedRoute mesh right rightSupported last)).atSheet
        (RouteWords.directedRoute mesh right rightSupported
          last).sheet).readings point := by
  cases edgeEq
  cases directionEq
  rfl

/-- Equal lifted edges and equal lookup directions identify the actual
cached point reading, even when the original fragment faces differ. -/
theorem canonicalPoint_eq {left right : RootedWords.LiftedFragment axes
  domains mesh source count target}
    (edgeEq : left.occurrence.side.edge = right.occurrence.side.edge)
    (directionEq : (RouteWords.routeForward left) =
      (RouteWords.routeForward right))
    (shared : Face.CommonMeshes.FaceSharedMeshes budgets numerics) (point :
      Gaussian.Basic.Canonical) :
    (RouteCancellation.canonicalPoint left) shared point =
      (RouteCancellation.canonicalPoint right) shared point :=
  RouteCancellation.directed_point_eq _ _ edgeEq directionEq shared point

/-- Root agreement at the original query junction identifies the lifted
edge; matching source coordinates alone would not justify cancellation. -/
theorem canonicalPoint_eq_of_junction {left right :
  RootedWords.LiftedFragment axes domains mesh source count target}
    (joined : left.last = right.first) (roots : Gaussian.Equivalence.NamedEquivalent left.lastName right.firstName)
    (startEq : left.fragment.source.start = right.fragment.source.start)
    (finishEq : left.fragment.source.finish = right.fragment.source.finish)
    (directionEq : (RouteWords.routeForward left) =
      (RouteWords.routeForward right))
    (shared : Face.CommonMeshes.FaceSharedMeshes budgets numerics) (point :
      Gaussian.Basic.Canonical) :
    (RouteCancellation.canonicalPoint left) shared point =
      (RouteCancellation.canonicalPoint right) shared point :=
  RouteCancellation.canonicalPoint_eq
    (left.occurrence.edge_eq_of_query_junction right.occurrence joined roots startEq finishEq)
    directionEq shared point

/-- A stationary partial fragment contributes exactly zero in its own
cached route, irrespective of which incident face was selected. -/
theorem routeValue_stationary (piece : RootedWords.LiftedFragment axes
  domains mesh source count target)
    (stationary : piece.last = piece.first) (shared :
      Face.CommonMeshes.FaceSharedMeshes budgets numerics) :
    (RouteContacts.routeValue piece)
      (RouteWords.canonicalRoute piece) shared = 0 := by
  rw [RouteCancellation.routeValue_eq, stationary]
  ring1

/-- The connected remaining fragments on one original directed edge telescope to the last reading minus the retained
previous endpoint.

Each original root junction identifies the shared cache used for the cancellation. -/
private theorem tail_telescope (previous : RootedWords.LiftedFragment axes
  domains mesh source count target)
    {pieces : List (RootedWords.LiftedFragment axes domains mesh source
      count target)}
    {last : Gaussian.Basic.Canonical} {lastName : Gaussian.Name.Basic.Named}
    (word : RootedWords.LiftedFragment.RootedWord pieces previous.last
      previous.lastName last lastName)
    (same : ∀ piece ∈ pieces, previous.fragment.source.start = piece.fragment.source.start ∧
      previous.fragment.source.finish = piece.fragment.source.finish ∧
        (RouteWords.routeForward previous) =
        (RouteWords.routeForward piece))
    (shared : Face.CommonMeshes.FaceSharedMeshes budgets numerics) :
    Gaussian.Norm.Sum.Basic.gaussianSum (pieces.map (fun piece =>
      (RouteContacts.routeValue piece)
      (RouteWords.canonicalRoute piece) shared)) =
      (RouteCancellation.canonicalPoint previous) shared last -
        (RouteCancellation.canonicalPoint previous) shared previous.last :=
        by
  cases word with
  | nil coordinate root =>
      change (0 : Gaussian.Basic.Canonical) = _ - _
      rw [coordinate]
      ring1
  | @cons piece rest first last firstName lastName joined roots tail =>
      obtain ⟨roots⟩ := roots
      have head := same piece List.mem_cons_self
      have equal := RouteCancellation.canonicalPoint_eq_of_junction joined
        roots head.1 head.2.1 head.2.2 shared
      have remaining : ∀ child : RootedWords.LiftedFragment axes domains
        mesh source count target, child ∈ rest → piece.fragment.source.start = child.fragment.source.start ∧
          piece.fragment.source.finish = child.fragment.source.finish ∧
            (RouteWords.routeForward piece) =
            (RouteWords.routeForward child) := by
        intro child member
        have childData := same child (List.mem_cons_of_mem _ member)
        exact ⟨head.1.symm.trans childData.1, head.2.1.symm.trans childData.2.1, head.2.2.symm.trans childData.2.2⟩
      change (RouteContacts.routeValue piece)
        (RouteWords.canonicalRoute piece) shared +
        Gaussian.Norm.Sum.Basic.gaussianSum _ = _
      rw [RouteCancellation.tail_telescope piece tail
        remaining shared, RouteCancellation.routeValue_eq, ← equal, ← equal,
        ← equal, joined]
      ring1
termination_by pieces.length
decreasing_by
  subst pieces
  exact Nat.lt_succ_self _

end Purelib.Curves.Hyperelliptic.Meshes.PuncturedGrid.Fragment.RouteCancellation

namespace Purelib.Curves.Hyperelliptic.Meshes.PuncturedGrid.Fragment.RouteCancellation.RootedWord

/-- A whole connected group on one original containing edge telescopes in
its actual canonical route. Every original root junction is consumed. -/
theorem canonical_telescope {head : RootedWords.LiftedFragment axes domains
  mesh source count target}
    {pieces : List (RootedWords.LiftedFragment axes domains mesh source
      count target)}
    {first last : Gaussian.Basic.Canonical} {firstName lastName : Gaussian.Name.Basic.Named}
    (word : RootedWords.LiftedFragment.RootedWord (head :: pieces) first
      firstName last lastName)
    (same : ∀ piece ∈ pieces, head.fragment.source.start = piece.fragment.source.start ∧
      head.fragment.source.finish = piece.fragment.source.finish ∧
        (RouteWords.routeForward head) =
        (RouteWords.routeForward piece))
    (shared : Face.CommonMeshes.FaceSharedMeshes budgets numerics) :
    Gaussian.Norm.Sum.Basic.gaussianSum ((head :: pieces).map (fun piece =>
      (RouteContacts.routeValue piece)
      (RouteWords.canonicalRoute piece) shared)) =
      (RouteCancellation.canonicalPoint head) shared last -
        (RouteCancellation.canonicalPoint head) shared first := by
  cases word with
  | cons head coordinate root tail =>
      change (RouteContacts.routeValue head)
        (RouteWords.canonicalRoute head) shared +
        Gaussian.Norm.Sum.Basic.gaussianSum _ = _
      rw [RouteCancellation.tail_telescope head tail same shared,
        RouteCancellation.routeValue_eq, coordinate]
      ring1

end Purelib.Curves.Hyperelliptic.Meshes.PuncturedGrid.Fragment.RouteCancellation.RootedWord

namespace Purelib.Curves.Hyperelliptic.Meshes.PuncturedGrid.Fragment.RouteCancellation.Junctions

/-- Read an actual adjacent pair from a retained word, including pairs
that occur after an arbitrary prefix. -/
theorem at_pair {left right : RootedWords.LiftedFragment axes domains mesh
  source count target}
    (before after : List (RootedWords.LiftedFragment axes domains mesh
      source count target))
    (junctions : WordJunctions.Junctions (before ++ left :: right :: after))
      : WordJunctions.Junction left right := by
  induction before with
  | nil => exact junctions.1
  | cons head tail ih =>
      cases tail with
      | nil => exact junctions.2.1
      | cons next tail => exact ih junctions.2

end Purelib.Curves.Hyperelliptic.Meshes.PuncturedGrid.Fragment.RouteCancellation.Junctions

end
